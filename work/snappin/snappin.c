/* snappin.c - capture part of the X11 screen (drag or --geometry) and save it
 * as a PNG. With --pin the capture also floats as a window at the same place.
 * Uses Xlib and stb_image_write.h (PNG encoding).
 *
 * Build (stb_image_write.h must be in the same directory):
 *   cc -O2 -o snappin snappin.c -lX11 -lm
 * Run: ./snappin --help
 *
 * Flow: parse options -> grab one image (drag selection or fixed area) ->
 * save / copy / pin it -> if we still own the CLIPBOARD, keep serving it from
 * a background process until something else is copied (like xclip does).
 */
#define _DEFAULT_SOURCE
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xatom.h>
#include <X11/keysym.h>
#include <X11/cursorfont.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <signal.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#define VERSION    "1.1"
#define BORDER_RGB 0x3daee9   /* pin border and selection frame color */
#define DCLICK_MS  350        /* max gap between clicks of a double click */
#define MAX_PIXELS 40000000.0 /* do not zoom beyond this many pixels */
#define MAX_XFERS  16         /* concurrent INCR clipboard transfers */
#define XFER_TIMEOUT_MS 5000

static struct {
    int pin, nosave, clipboard, quiet, full;
    const char *geometry, *output;
    double delay;
} opt;

static char out_dir[4096];   /* where timestamped files go */
static const char *out_file; /* file name from -o (or "-"), used for the first save only */

static Display *dpy;
static Window root;
static Visual *vis;
static int depth, SW, SH; /* color depth, screen width/height */
static GC gc;

/* a captured image: w*h pixels, 3 bytes (R, G, B) each, rows top to bottom */
typedef struct { int w, h; uint8_t *rgb; } Img;

static int64_t now_ms(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t)tv.tv_sec * 1000 + tv.tv_usec / 1000;
}

static int clamp(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }

/* informational message on stderr, silenced by -q */
static void info(const char *fmt, ...)
{
    if (opt.quiet)
        return;
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
}

/* point fd at /dev/null (detaches stdin/stdout/stderr) */
static void null_fd(int fd)
{
    int n = open("/dev/null", O_RDWR);
    if (n >= 0 && n != fd) {
        dup2(n, fd);
        close(n);
    }
}

/* ---------- pixel value <-> RGB (TrueColor visuals) ---------- */

/* per channel (R, G, B): bits used in a pixel value, their shift, largest value */
static struct { uint32_t mask, max; int shift; } ch[3];

static void chan_init(void)
{
    uint32_t m[3] = { vis->red_mask, vis->green_mask, vis->blue_mask };
    for (int i = 0; i < 3; i++) {
        ch[i].mask = m[i];
        while (m[i] && !(m[i] & 1)) {
            m[i] >>= 1;
            ch[i].shift++;
        }
        ch[i].max = m[i];
    }
}

/* 0xRRGGBB -> pixel value */
static uint32_t rgb_pixel(uint32_t rgb)
{
    uint32_t p = 0;
    for (int i = 0; i < 3; i++)
        p |= (((rgb >> (16 - 8 * i)) & 255) * ch[i].max / 255) << ch[i].shift;
    return p;
}

/* pixel value -> 3 bytes R, G, B */
static void pixel_rgb(uint32_t p, uint8_t *out)
{
    for (int i = 0; i < 3; i++)
        out[i] = ch[i].max ? ((p & ch[i].mask) >> ch[i].shift) * 255 / ch[i].max : 0;
}

/* convert a grabbed XImage to an Img and free it. 0 = the grab failed */
static int img_from(XImage *xi, Img *im)
{
    if (!xi) {
        fprintf(stderr, "Could not grab the screen. Is this an X11 session?\n");
        return 0;
    }
    im->w = xi->width;
    im->h = xi->height;
    im->rgb = malloc((size_t)im->w * im->h * 3);
    for (int y = 0; y < im->h; y++)
        for (int x = 0; x < im->w; x++)
            pixel_rgb(XGetPixel(xi, x, y), im->rgb + ((size_t)y * im->w + x) * 3);
    XDestroyImage(xi);
    return 1;
}

/* ---------- PNG output ---------- */

/* growable byte buffer for in-memory PNGs; fail is set if memory ran out */
typedef struct { uint8_t *p; size_t len, cap; int fail; } Buf;

/* stb write callback: append n bytes */
static void buf_put(void *ctx, void *data, int n)
{
    Buf *b = ctx;
    if (b->fail || n <= 0)
        return;
    if (b->len + n > b->cap) {
        size_t cap = b->cap ? b->cap : 65536;
        while (cap < b->len + n)
            cap *= 2;
        uint8_t *q = realloc(b->p, cap);
        if (!q) {
            b->fail = 1;
            return;
        }
        b->p = q;
        b->cap = cap;
    }
    memcpy(b->p + b->len, data, n);
    b->len += n;
}

/* encode to PNG in memory. 1 = ok; the caller frees b->p either way */
static int png_mem(const Img *im, Buf *b)
{
    memset(b, 0, sizeof *b);
    return stbi_write_png_to_func(buf_put, b, im->w, im->h, 3, im->rgb, im->w * 3) && !b->fail;
}

/* Save as PNG: to the -o name the first time, later to
 * <out_dir>/snappin-YYYYmmdd-HHMMSS[-N].png. Prints the path. 1 = ok */
static int img_save(const Img *im)
{
    char path[4200], stamp[32];
    const char *f = out_file;
    out_file = NULL;
    if (f && !strcmp(f, "-")) { /* stdout */
        Buf b;
        int ok = png_mem(im, &b) && fwrite(b.p, 1, b.len, stdout) == b.len && fflush(stdout) == 0;
        free(b.p);
        null_fd(1); /* close the pipe so the reader sees EOF while we keep running */
        if (!ok)
            fprintf(stderr, "Could not write the PNG to stdout\n");
        return ok;
    }
    if (f) {
        snprintf(path, sizeof path, "%s", f);
    } else {
        time_t t = time(NULL);
        strftime(stamp, sizeof stamp, "%Y%m%d-%H%M%S", localtime(&t));
        snprintf(path, sizeof path, "%s/snappin-%s.png", out_dir, stamp);
        for (int i = 2; access(path, F_OK) == 0 && i < 1000; i++) /* same second */
            snprintf(path, sizeof path, "%s/snappin-%s-%d.png", out_dir, stamp, i);
    }
    if (!stbi_write_png(path, im->w, im->h, 3, im->rgb, im->w * 3)) {
        fprintf(stderr, "Could not save: %s\n", path);
        return 0;
    }
    if (!opt.quiet) {
        printf("%s\n", path); /* the saved path goes to stdout for scripts */
        fflush(stdout);
    }
    return 1;
}

/* ---------- clipboard (we own the CLIPBOARD selection) ----------
 *
 * X11 has no shared clipboard buffer. Copying means owning the CLIPBOARD
 * selection: when a program pastes, we get a SelectionRequest, write the data
 * into a property on its window and reply with SelectionNotify. So the PNG
 * stays in memory for as long as we own the selection.
 */

static Atom a_clipboard, a_targets, a_timestamp, a_png, a_incr, a_time;
static Window clip_win;  /* hidden window that owns the selection */
static size_t chunk_max; /* largest property we write in one request */
static struct { uint8_t *data; size_t len; Time time; int owned; } clip;

/* INCR transfer for data larger than one request: the next chunk is sent each
 * time the requestor deletes the property. Each transfer has its own copy so
 * it can finish even if the clipboard changes meanwhile. */
typedef struct { Window req; Atom prop; uint8_t *data; size_t len, off; int64_t last; } Xfer;
static Xfer xfers[MAX_XFERS];
static int nxfers;

static void clip_drop(void)
{
    free(clip.data);
    clip.data = NULL;
    clip.owned = 0;
}

static void xfer_end(int i)
{
    XSelectInput(dpy, xfers[i].req, NoEventMask);
    free(xfers[i].data);
    xfers[i] = xfers[--nxfers];
}

/* Current X server time, for taking the selection without a user event:
 * appending zero bytes to a property still produces a timestamped PropertyNotify. */
static Time server_time(void)
{
    XEvent e;
    XChangeProperty(dpy, clip_win, a_time, XA_INTEGER, 32, PropModeAppend, NULL, 0);
    XWindowEvent(dpy, clip_win, PropertyChangeMask, &e);
    return e.xproperty.time;
}

/* encode the image and take CLIPBOARD. t = time of the user event. 1 = ok */
static int clip_set(const Img *im, Time t)
{
    Buf b;
    if (!png_mem(im, &b)) {
        free(b.p);
        fprintf(stderr, "Could not encode the PNG\n");
        return 0;
    }
    free(clip.data);
    clip.data = b.p;
    clip.len = b.len;
    clip.time = t;
    XSetSelectionOwner(dpy, a_clipboard, clip_win, t);
    clip.owned = XGetSelectionOwner(dpy, a_clipboard) == clip_win;
    if (!clip.owned) {
        clip_drop();
        fprintf(stderr, "Could not take the clipboard\n");
        return 0;
    }
    info("Copied %dx%d PNG to the clipboard (image/png)\n", im->w, im->h);
    return 1;
}

/* Answer a paste request for TARGETS, TIMESTAMP or image/png; refuse others. */
static void clip_request(XSelectionRequestEvent *r)
{
    XSelectionEvent ev = { .type = SelectionNotify, .display = r->display, .requestor = r->requestor,
                           .selection = r->selection, .target = r->target, .time = r->time };
    Atom prop = r->property != None ? r->property : r->target; /* obsolete clients */
    /* format 32 property data is an array of long in Xlib, even on 64-bit */
    long v[3];
    int n = 0, fmt = 32;
    Atom type = XA_ATOM;
    const void *data = v;

    if (!clip.owned || r->selection != a_clipboard) {
        n = -1;
    } else if (r->target == a_targets) {
        v[0] = a_targets, v[1] = a_timestamp, v[2] = a_png, n = 3;
    } else if (r->target == a_timestamp) {
        v[0] = (long)clip.time, n = 1, type = XA_INTEGER;
    } else if (r->target == a_png && clip.len <= chunk_max) { /* send all at once */
        data = clip.data, n = (int)clip.len, fmt = 8, type = a_png;
    } else if (r->target == a_png && nxfers < MAX_XFERS && (data = malloc(clip.len))) {
        /* too big: start an INCR transfer by writing the total size */
        Xfer *x = &xfers[nxfers++];
        *x = (Xfer){ r->requestor, prop, (uint8_t *)data, clip.len, 0, now_ms() };
        memcpy(x->data, clip.data, clip.len);
        XSelectInput(dpy, r->requestor, PropertyChangeMask); /* to see it delete the property */
        v[0] = (long)clip.len, n = 1, type = a_incr, data = v;
    } else {
        n = -1;
    }
    if (n >= 0) {
        XChangeProperty(dpy, r->requestor, prop, type, fmt, PropModeReplace, (const unsigned char *)data, n);
        ev.property = prop;
    } /* else property = None: refused */
    XSendEvent(dpy, r->requestor, False, NoEventMask, (XEvent *)&ev);
}

/* A property was deleted: if it is an INCR transfer's, send the next chunk
 * (a zero-length chunk ends it). Returns 1 if the event was ours. */
static int xfer_event(XPropertyEvent *e)
{
    for (int i = 0; e->state == PropertyDelete && i < nxfers; i++) {
        Xfer *x = &xfers[i];
        if (x->req != e->window || x->prop != e->atom)
            continue;
        size_t n = x->len - x->off < chunk_max ? x->len - x->off : chunk_max;
        XChangeProperty(dpy, x->req, x->prop, a_png, 8, PropModeReplace, x->data + x->off, (int)n);
        x->off += n;
        x->last = now_ms();
        if (n == 0)
            xfer_end(i);
        return 1;
    }
    return 0;
}

/* Wait for the next X event, answering clipboard events on the way.
 * Returns 1 with another event in e, or 0 after up to 1 s without one.
 * Also drops INCR transfers whose requestor went away. */
static int next_event(XEvent *e)
{
    if (!XPending(dpy)) {
        fd_set fds;
        FD_ZERO(&fds);
        FD_SET(ConnectionNumber(dpy), &fds);
        struct timeval tv = { 1, 0 };
        select(ConnectionNumber(dpy) + 1, &fds, NULL, NULL, &tv);
    }
    for (int i = nxfers - 1; i >= 0; i--)
        if (now_ms() - xfers[i].last > XFER_TIMEOUT_MS)
            xfer_end(i);
    while (XPending(dpy)) {
        XNextEvent(dpy, e);
        if (e->type == SelectionRequest)
            clip_request(&e->xselectionrequest);
        else if (e->type == SelectionClear && e->xselectionclear.selection == a_clipboard)
            clip_drop(); /* someone else copied something */
        else if (!(e->type == PropertyNotify && xfer_event(&e->xproperty)))
            return 1;
    }
    return 0;
}

/* a borderless, always-on-top window (override-redirect: the WM leaves it alone) */
static Window popup(int x, int y, int w, int h, Pixmap bg, Cursor cur, long events)
{
    XSetWindowAttributes a = { .override_redirect = True, .background_pixmap = bg,
                               .cursor = cur, .event_mask = events };
    Window win = XCreateWindow(dpy, root, x, y, w, h, 0, CopyFromParent, InputOutput, CopyFromParent,
                               CWOverrideRedirect | CWBackPixmap | CWCursor | CWEventMask, &a);
    XMapRaised(dpy, win);
    return win;
}

/* ---------- area selection ----------
 *
 * The screen is grabbed once and shown frozen and darkened in a fullscreen
 * window; the box shows the bright original. The result is cut from the same
 * frozen shot, so what you see is exactly what you get.
 */

static struct {
    Window win;
    Pixmap orig, dark, back;  /* bright screen, darkened screen, back buffer */
    int x0, y0, x1, y1;       /* current box (x1, y1 exclusive) */
} sel;

/* dark screen + bright box + frame + "W x H" label, drawn via the back buffer */
static void sel_draw(void)
{
    int w = sel.x1 - sel.x0, h = sel.y1 - sel.y0;
    XCopyArea(dpy, sel.dark, sel.back, gc, 0, 0, SW, SH, 0, 0);
    if (w > 0 && h > 0) {
        char t[32];
        int n = snprintf(t, sizeof t, "%d x %d", w, h);
        int ly = sel.y0 > 24 ? sel.y0 - 6 : sel.y1 + 16; /* above the box, or below */
        XCopyArea(dpy, sel.orig, sel.back, gc, sel.x0, sel.y0, w, h, sel.x0, sel.y0);
        XSetForeground(dpy, gc, rgb_pixel(BORDER_RGB));
        XDrawRectangle(dpy, sel.back, gc, sel.x0 - 1, sel.y0 - 1, w + 1, h + 1);
        XSetForeground(dpy, gc, rgb_pixel(0x000000));
        XDrawString(dpy, sel.back, gc, sel.x0 + 1, ly + 1, t, n); /* shadow */
        XSetForeground(dpy, gc, rgb_pixel(0xffffff));
        XDrawString(dpy, sel.back, gc, sel.x0, ly, t, n);
    }
    XCopyArea(dpy, sel.back, sel.win, gc, 0, 0, SW, SH, 0, 0);
}

/* Let the user drag a box. 1 = got it in *im (top left at *px, *py), 0 = cancelled/failed */
static int select_area(Img *im, int *px, int *py)
{
    XImage *shot = XGetImage(dpy, root, 0, 0, SW, SH, AllPlanes, ZPixmap);
    if (!shot)
        return img_from(NULL, im); /* prints the error */
    sel.orig = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.dark = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.back = XCreatePixmap(dpy, root, SW, SH, depth);
    XPutImage(dpy, sel.orig, gc, shot, 0, 0, 0, 0, SW, SH);
    /* halve every channel */
    if (depth == 24 && shot->bits_per_pixel == 32) { /* 8-bit channels: halve each byte */
        for (size_t i = 0, n = (size_t)shot->bytes_per_line * SH; i < n; i++)
            shot->data[i] = (char)((uint8_t)shot->data[i] >> 1);
    } else {
        for (int y = 0; y < SH; y++)
            for (int x = 0; x < SW; x++) {
                uint32_t p = XGetPixel(shot, x, y), q = 0;
                for (int i = 0; i < 3; i++)
                    q |= ((p & ch[i].mask) >> 1) & ch[i].mask;
                XPutPixel(shot, x, y, q);
            }
    }
    XPutImage(dpy, sel.dark, gc, shot, 0, 0, 0, 0, SW, SH);
    XDestroyImage(shot);

    Cursor cross = XCreateFontCursor(dpy, XC_crosshair);
    long mask = ButtonPressMask | ButtonReleaseMask | PointerMotionMask;
    sel.win = popup(0, 0, SW, SH, sel.dark, cross, ExposureMask | KeyPressMask | mask);
    XSync(dpy, False);
    /* grab input; retry for up to 1 s since the hotkey that started us may still hold a grab */
    for (int i = 0; i < 40 && XGrabPointer(dpy, sel.win, False, mask, GrabModeAsync, GrabModeAsync,
                                           None, cross, CurrentTime) != GrabSuccess; i++)
        usleep(25000);
    for (int i = 0; i < 40 && XGrabKeyboard(dpy, sel.win, False, GrabModeAsync, GrabModeAsync,
                                            CurrentTime) != GrabSuccess; i++)
        usleep(25000);

    int sx = 0, sy = 0, pressing = 0, done = -1; /* drag start, button held, result */
    sel.x0 = sel.x1 = sel.y0 = sel.y1 = 0;
    sel_draw();
    while (done < 0) {
        XEvent e;
        if (!next_event(&e) || e.xany.window != sel.win)
            continue;
        if (e.type == KeyPress && XLookupKeysym(&e.xkey, 0) == XK_Escape)
            done = 0;
        else if (e.type == ButtonPress && e.xbutton.button == Button3)
            done = 0;
        else if (e.type == ButtonPress && e.xbutton.button == Button1) {
            sel.x0 = sel.x1 = sx = clamp(e.xbutton.x, 0, SW);
            sel.y0 = sel.y1 = sy = clamp(e.xbutton.y, 0, SH);
            pressing = 1;
        } else if (pressing && (e.type == MotionNotify || e.type == ButtonRelease)) {
            while (e.type == MotionNotify && XCheckTypedWindowEvent(dpy, sel.win, MotionNotify, &e))
                ; /* use only the latest position */
            int x = clamp(e.xbutton.x, 0, SW), y = clamp(e.xbutton.y, 0, SH); /* same layout in xmotion */
            sel.x0 = x < sx ? x : sx, sel.x1 = x < sx ? sx : x;
            sel.y0 = y < sy ? y : sy, sel.y1 = y < sy ? sy : y;
            if (e.type == ButtonRelease && e.xbutton.button == Button1) {
                pressing = 0;
                if (sel.x1 - sel.x0 >= 3 && sel.y1 - sel.y0 >= 3)
                    done = 1;
                else
                    sel.x1 = sel.x0, sel.y1 = sel.y0; /* too small: select again */
            }
        }
        if (done < 0)
            sel_draw();
    }
    XUngrabPointer(dpy, CurrentTime);
    XUngrabKeyboard(dpy, CurrentTime);
    XDestroyWindow(dpy, sel.win);
    if (done) {
        *px = sel.x0;
        *py = sel.y0;
        done = img_from(XGetImage(dpy, sel.orig, sel.x0, sel.y0, sel.x1 - sel.x0, sel.y1 - sel.y0,
                                  AllPlanes, ZPixmap), im);
    } else {
        info("Cancelled\n");
    }
    XFreePixmap(dpy, sel.orig);
    XFreePixmap(dpy, sel.dark);
    XFreePixmap(dpy, sel.back);
    return done;
}

/* ---------- pin (floating window) ---------- */

static struct {
    Window win;
    Pixmap pm;              /* the image drawn at the current scale, with a 1 px border */
    const Img *img;         /* original pixels (copy/save always use these) */
    int x, y, w, h, dx, dy; /* window position and size; dx/dy = grab offset while dragging */
    double scale;
    Time last_click;        /* for double click detection */
} pin;

/* Rebuild the pixmap at the current scale (bilinear) and move/resize the
 * window. Fixed point: positions are in 1/256 pixels, so f >> 8 is the source
 * pixel and f & 255 the weight of its right/lower neighbour. */
static void pin_render(void)
{
    const Img *s = pin.img;
    int w = (int)(s->w * pin.scale + 0.5), h = (int)(s->h * pin.scale + 0.5);
    w = w < 1 ? 1 : w;
    h = h < 1 ? 1 : h;
    XImage *xi = XCreateImage(dpy, vis, depth, ZPixmap, 0, NULL, w, h, 32, 0);
    xi->data = malloc((size_t)xi->bytes_per_line * h);
    for (int y = 0; y < h; y++) {
        int64_t fy = (int64_t)(2 * y + 1) * s->h * 128 / h - 128; /* pixel center, minus half */
        fy = fy < 0 ? 0 : fy;
        int y0 = fy >> 8, ty = fy & 255, y1 = y0 + 1 < s->h ? y0 + 1 : y0;
        for (int x = 0; x < w; x++) {
            int64_t fx = (int64_t)(2 * x + 1) * s->w * 128 / w - 128;
            fx = fx < 0 ? 0 : fx;
            int x0 = fx >> 8, tx = fx & 255, x1 = x0 + 1 < s->w ? x0 + 1 : x0;
            /* the 4 source pixels around the point: a b / c d */
            const uint8_t *a = s->rgb + ((size_t)y0 * s->w + x0) * 3, *b = s->rgb + ((size_t)y0 * s->w + x1) * 3,
                          *c = s->rgb + ((size_t)y1 * s->w + x0) * 3, *d = s->rgb + ((size_t)y1 * s->w + x1) * 3;
            uint32_t v = 0;
            for (int i = 0; i < 3; i++) {
                uint32_t top = a[i] * (256 - tx) + b[i] * tx, bot = c[i] * (256 - tx) + d[i] * tx;
                v = v << 8 | ((top * (256 - ty) + bot * ty) >> 16);
            }
            XPutPixel(xi, x, y, rgb_pixel(v));
        }
    }
    if (pin.pm)
        XFreePixmap(dpy, pin.pm);
    pin.pm = XCreatePixmap(dpy, root, w, h, depth);
    XPutImage(dpy, pin.pm, gc, xi, 0, 0, 0, 0, w, h);
    XDestroyImage(xi);
    XSetForeground(dpy, gc, rgb_pixel(BORDER_RGB));
    XDrawRectangle(dpy, pin.pm, gc, 0, 0, w - 1, h - 1);
    pin.w = w;
    pin.h = h;
    XMoveResizeWindow(dpy, pin.win, pin.x, pin.y, w, h);
    XCopyArea(dpy, pin.pm, pin.win, gc, 0, 0, w, h, 0, 0);
}

/* set the zoom to s (0.1x .. 8x), keeping screen point rx, ry in place */
static void pin_zoom(double s, int rx, int ry)
{
    s = s < 0.1 ? 0.1 : s > 8.0 ? 8.0 : s;
    if (s > 0.999 && s < 1.001)
        s = 1.0; /* snap to exactly 1x after rounding errors */
    if (s == pin.scale || (double)pin.img->w * s * pin.img->h * s > MAX_PIXELS)
        return;
    pin.x = rx - (int)((rx - pin.x) * s / pin.scale);
    pin.y = ry - (int)((ry - pin.y) * s / pin.scale);
    pin.scale = s;
    pin_render();
}

/* Show img at screen position x, y until the window is closed.
 * drag = move, wheel = zoom, Ctrl+C = copy, Ctrl+S = save, 1 = actual size,
 * double click / Esc = close */
static void pin_run(const Img *img, int x, int y)
{
    pin.img = img;
    pin.x = x;
    pin.y = y;
    pin.scale = 1.0;
    pin.win = popup(x, y, img->w, img->h, None, XCreateFontCursor(dpy, XC_fleur),
                    ExposureMask | ButtonPressMask | Button1MotionMask | KeyPressMask | EnterWindowMask);
    XStoreName(dpy, pin.win, "snappin");
    pin_render();
    while (pin.win) {
        XEvent e;
        if (!next_event(&e) || e.xany.window != pin.win)
            continue;
        XButtonEvent *b = &e.xbutton;
        KeySym k = e.type == KeyPress ? XLookupKeysym(&e.xkey, 0) : NoSymbol; /* index 0 ignores Shift */
        int ctrl = e.type == KeyPress && (e.xkey.state & ControlMask);
        if (e.type == Expose)
            XCopyArea(dpy, pin.pm, pin.win, gc, 0, 0, pin.w, pin.h, 0, 0);
        else if (e.type == EnterNotify) /* override-redirect windows get no focus from the WM */
            XSetInputFocus(dpy, pin.win, RevertToPointerRoot, CurrentTime);
        else if (e.type == ButtonPress && b->button == Button4)
            pin_zoom(pin.scale * 1.1, b->x_root, b->y_root);
        else if (e.type == ButtonPress && b->button == Button5)
            pin_zoom(pin.scale / 1.1, b->x_root, b->y_root);
        else if ((e.type == ButtonPress && b->button == Button1 && b->time - pin.last_click < DCLICK_MS) ||
                 k == XK_Escape) {
            XDestroyWindow(dpy, pin.win);
            XFreePixmap(dpy, pin.pm);
            pin.win = 0;
        } else if (e.type == ButtonPress && b->button == Button1) {
            pin.last_click = b->time;
            pin.dx = b->x_root - pin.x; /* where inside the window we grabbed it */
            pin.dy = b->y_root - pin.y;
            XRaiseWindow(dpy, pin.win);
        } else if (e.type == MotionNotify) { /* only while button 1 is held */
            while (XCheckTypedWindowEvent(dpy, pin.win, MotionNotify, &e))
                ; /* use only the latest position */
            pin.x = e.xmotion.x_root - pin.dx;
            pin.y = e.xmotion.y_root - pin.dy;
            XMoveWindow(dpy, pin.win, pin.x, pin.y);
        } else if (ctrl && k == XK_c)
            clip_set(img, e.xkey.time);
        else if (ctrl && k == XK_s)
            img_save(img);
        else if (!ctrl && k == XK_1)
            pin_zoom(1.0, pin.x, pin.y);
    }
}

/* ---------- main ---------- */

static int on_xerror(Display *d, XErrorEvent *e)
{
    (void)d; (void)e; /* ignore errors such as requests on windows that are already gone */
    return 0;
}

static void usage(void)
{
    fputs(
"Usage: snappin [options]\n"
"Capture part of the X11 screen and save it as a PNG.\n"
"With no options, drag to select an area; it is saved in the current\n"
"directory as snappin-YYYYmmdd-HHMMSS.png.\n"
"\n"
"  -g, --geometry WxH+X+Y  capture this area instead of selecting with the mouse\n"
"                          (X11 geometry; negative X/Y count from the right/bottom)\n"
"  -f, --fullscreen        capture the whole screen\n"
"  -o, --output PATH       where to save: a file name, a directory (ending in /\n"
"                          or existing), or - for stdout (default: .)\n"
"  -n, --no-save           do not save a file\n"
"  -c, --clipboard         copy the PNG to the CLIPBOARD selection (image/png)\n"
"  -p, --pin               also show the capture as a floating window at the\n"
"                          same place\n"
"  -d, --delay SEC         wait SEC seconds before capturing (decimals allowed)\n"
"  -q, --quiet             print nothing except errors\n"
"  -h, --help              show this help\n"
"  -V, --version           show the version\n"
"\n"
"Selection: drag = select, Esc / right click = cancel\n"
"Pin window: drag = move, wheel = zoom, 1 = actual size, Ctrl+C = copy,\n"
"  Ctrl+S = save (to the -o place), double click / Esc = close\n"
"\n"
"The saved file path is printed to stdout. Exit status: 0 = ok,\n"
"1 = cancelled or failed, 2 = bad usage.\n"
"\n"
"Examples:\n"
"  snappin                             select an area, save it in .\n"
"  snappin -p -n                       select an area and pin it, no file\n"
"  snappin -c -n                       select an area, clipboard only\n"
"  snappin -g 800x600+100+50 -o a.png  fixed area to a.png\n"
"  snappin -f -d 3 -o ~/Pictures/      whole screen after 3 s\n"
"  snappin -o - | convert - out.jpg    PNG to stdout\n", stdout);
}

static int bad_usage(const char *msg, const char *arg)
{
    fprintf(stderr, "snappin: %s%s%s\nTry 'snappin --help'.\n", msg, arg ? ": " : "", arg ? arg : "");
    return 2;
}

/* Fill out_dir / out_file from -o:
 *   none or "-"            -> timestamped files in . ("-" = first image to stdout)
 *   dir/ or existing dir   -> timestamped files there (created if needed)
 *   anything else          -> that file; later saves (Ctrl+S) go next to it
 * Returns 0 = ok, otherwise an exit status. */
static int setup_output(void)
{
    const char *o = opt.output ? opt.output : ".";
    struct stat st;
    size_t n = strlen(o);
    if (!n || n >= sizeof out_dir)
        return bad_usage("bad --output", o);
    strcpy(out_dir, o);
    if (o[n - 1] == '/' || (stat(o, &st) == 0 && S_ISDIR(st.st_mode))) {
        while (n > 1 && out_dir[n - 1] == '/') /* strip trailing slashes, keep "/" */
            out_dir[--n] = 0;
        if (mkdir(out_dir, 0755) && errno != EEXIST) {
            fprintf(stderr, "snappin: cannot create directory: %s\n", out_dir);
            return 1;
        }
        return 0;
    }
    out_file = o;
    char *s = strrchr(out_dir, '/'); /* out_dir = the directory part */
    if (!s || !strcmp(o, "-"))
        strcpy(out_dir, ".");
    else
        s[s == out_dir] = 0; /* keep "/" for files in the root directory */
    return 0;
}

int main(int argc, char **argv)
{
    static const struct option longopts[] = {
        { "geometry", required_argument, 0, 'g' }, { "fullscreen", no_argument, 0, 'f' },
        { "output", required_argument, 0, 'o' },   { "no-save", no_argument, 0, 'n' },
        { "clipboard", no_argument, 0, 'c' },      { "pin", no_argument, 0, 'p' },
        { "delay", required_argument, 0, 'd' },    { "quiet", no_argument, 0, 'q' },
        { "help", no_argument, 0, 'h' },           { "version", no_argument, 0, 'V' },
        { 0, 0, 0, 0 }
    };
    int c;
    char *end;
    while ((c = getopt_long(argc, argv, "g:fo:ncpd:qhV", longopts, NULL)) != -1) {
        switch (c) {
        case 'g': opt.geometry = optarg; break;
        case 'f': opt.full = 1; break;
        case 'o': opt.output = optarg; break;
        case 'n': opt.nosave = 1; break;
        case 'c': opt.clipboard = 1; break;
        case 'p': opt.pin = 1; break;
        case 'q': opt.quiet = 1; break;
        case 'h': usage(); return 0;
        case 'V': puts("snappin " VERSION); return 0;
        case 'd':
            opt.delay = strtod(optarg, &end);
            if (end == optarg || *end || opt.delay < 0 || opt.delay > 86400)
                return bad_usage("bad --delay", optarg);
            break;
        default: return 2; /* getopt already printed the error */
        }
    }
    if (optind < argc)
        return bad_usage("unexpected argument", argv[optind]);
    if (opt.geometry && opt.full)
        return bad_usage("use only one of --geometry and --fullscreen", NULL);
    if (opt.nosave && !opt.clipboard && !opt.pin)
        return bad_usage("--no-save needs --clipboard or --pin, or there is nothing to do", NULL);
    int status = setup_output();
    if (status)
        return status;

    signal(SIGPIPE, SIG_IGN); /* a closed stdout pipe (-o -) is reported, not fatal */
    if (!(dpy = XOpenDisplay(NULL))) {
        fprintf(stderr, "Cannot open the X11 display (DISPLAY). Run this in an X11 session.\n");
        return 1;
    }
    XSetErrorHandler(on_xerror);
    int scr = DefaultScreen(dpy);
    root = RootWindow(dpy, scr);
    vis = DefaultVisual(dpy, scr);
    depth = DefaultDepth(dpy, scr);
    SW = DisplayWidth(dpy, scr);
    SH = DisplayHeight(dpy, scr);
    if (vis->class != TrueColor) {
        fprintf(stderr, "Only TrueColor (24-bit) displays are supported.\n");
        return 1;
    }
    chan_init();
    gc = XCreateGC(dpy, root, 0, NULL);

    a_clipboard = XInternAtom(dpy, "CLIPBOARD", False);
    a_targets = XInternAtom(dpy, "TARGETS", False);
    a_timestamp = XInternAtom(dpy, "TIMESTAMP", False);
    a_png = XInternAtom(dpy, "image/png", False);
    a_incr = XInternAtom(dpy, "INCR", False);
    a_time = XInternAtom(dpy, "_SNAPPIN_TIME", False);
    clip_win = XCreateSimpleWindow(dpy, root, -10, -10, 1, 1, 0, 0, 0);
    XSelectInput(dpy, clip_win, PropertyChangeMask);
    /* max request size is in 4-byte units; leave room for the header */
    chunk_max = (size_t)XMaxRequestSize(dpy) * 4 - 1024;
    chunk_max = chunk_max > 256 * 1024 ? 256 * 1024 : chunk_max;

    /* fixed area from -g / -f, clipped to the screen */
    int x = 0, y = 0, w = SW, h = SH;
    if (opt.geometry) {
        unsigned int gw = 0, gh = 0; /* XParseGeometry wants unsigned int */
        int m = XParseGeometry(opt.geometry, &x, &y, &gw, &gh);
        if (!(m & WidthValue) || !(m & HeightValue) || !gw || !gh)
            return bad_usage("bad --geometry (want WxH+X+Y)", opt.geometry);
        w = gw > (unsigned)SW * 2 ? SW * 2 : (int)gw; /* cap so the math below cannot overflow */
        h = gh > (unsigned)SH * 2 ? SH * 2 : (int)gh;
        if (m & XNegative) x += SW - w;
        if (m & YNegative) y += SH - h;
        w = clamp(x + w, 0, SW) - clamp(x, 0, SW);
        h = clamp(y + h, 0, SH) - clamp(y, 0, SH);
        x = clamp(x, 0, SW);
        y = clamp(y, 0, SH);
        if (w < 1 || h < 1) {
            fprintf(stderr, "snappin: --geometry is outside the %dx%d screen\n", SW, SH);
            return 1;
        }
    }

    if (opt.delay > 0) {
        struct timespec ts = { (time_t)opt.delay, (long)((opt.delay - (time_t)opt.delay) * 1e9) };
        nanosleep(&ts, NULL);
    }

    Img im;
    int ok = opt.geometry || opt.full
                 ? img_from(XGetImage(dpy, root, x, y, w, h, AllPlanes, ZPixmap), &im)
                 : select_area(&im, &x, &y);
    if (!ok)
        return 1;
    if (!opt.nosave && !img_save(&im))
        status = 1;
    if (opt.clipboard && !clip_set(&im, server_time()))
        status = 1;
    if (opt.pin)
        pin_run(&im, x, y);
    free(im.rgb);

    if (clip.owned) {
        /* keep serving the clipboard in the background */
        info("Clipboard is kept by a background process until something else is copied.\n");
        XSync(dpy, False);
        pid_t pid = fork();
        if (pid > 0)
            _exit(status); /* parent returns to the shell; the child keeps the X connection */
        if (pid == 0) {
            setsid(); /* leave the terminal's session so closing it does not kill us */
            null_fd(0); /* and let $(snappin ...) and pipes finish */
            null_fd(1);
            null_fd(2);
        }
        XEvent e;
        while (clip.owned || nxfers)
            next_event(&e);
    }
    XCloseDisplay(dpy);
    return status;
}
