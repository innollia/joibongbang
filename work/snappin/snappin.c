/* snappin.c - capture part of the X11 screen (drag or --geometry) and save it
 * as a PNG. With --pin the capture also floats as a window at the exact same
 * position. Uses Xlib and stb_image_write.h (PNG encoding).
 *
 * Build (stb_image_write.h must be in the same directory):
 *   cc -O2 -o snappin snappin.c -lX11 -lm
 *   Debian/Ubuntu: sudo apt install build-essential libx11-dev
 * Run: ./snappin --help
 *
 * Capture screen: drag = select area, Esc / right click = cancel
 * Pin:            drag = move, wheel = zoom, Ctrl+wheel = opacity
 *                 Ctrl+C = copy PNG to CLIPBOARD, Ctrl+S = save, 1 = actual size,
 *                 N = new capture, double click / Esc = close, right click = menu
 *
 * --clipboard and Ctrl+C make snappin itself the owner of the CLIPBOARD
 * selection with an image/png target, so this works:
 *   xclip -o -sel clip -t image/png > image.png
 * If the clipboard is still held when snappin would exit, it keeps serving it
 * from a background process until something else is copied.
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

#define BORDER_RGB 0x3daee9 /* pin border and selection frame color */
#define FLASH_MS   400      /* how long the border flashes after copy/save */
#define DCLICK_MS  350      /* max gap between clicks of a double click */
#define MAX_PINS   256      /* max number of floating windows at once */
#define MAX_PIXELS 40000000.0 /* do not zoom beyond this many pixels */
#define MAX_XFERS  16          /* concurrent INCR clipboard transfers */
#define XFER_TIMEOUT_MS 5000
#define VERSION    "1.0"

/* command line options */
static struct {
    int pin, nosave, clipboard, quiet, full;
    const char *geometry, *output;
    double delay;
} opt;

static char out_dir[4096];   /* where timestamped files go */
static const char *out_file; /* explicit file name from -o (or "-"), used once */
static int out_file_used, captured, exit_code; /* captured = number of captures taken */

/* X11 state shared by the whole program */
static Display *dpy;
static Window root;
static Visual *vis;
static int depth, SW, SH; /* color depth, screen width/height */
static GC gc;
static XFontStruct *font;
static Atom a_opacity;  /* _NET_WM_WINDOW_OPACITY, read by compositors */
static Cursor cur_cross, cur_move;
static unsigned long border_px;
static long capture_at; /* scheduled time (ms) of a new capture, 0 = none */

/* wall clock in milliseconds */
static long now_ms(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000L + tv.tv_usec / 1000;
}

/* round to the nearest int (halves away from zero) */
static int iround(double v) { return v < 0 ? (int)(v - 0.5) : (int)(v + 0.5); }

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

/* point fd at /dev/null (used to detach stdin/stdout/stderr) */
static void null_fd(int fd)
{
    int n = open("/dev/null", O_RDWR);
    if (n >= 0 && n != fd) {
        dup2(n, fd);
        close(n);
    }
}

/* ---------- pixel value <-> RGB ---------- */

/* One color channel of a TrueColor visual: the bits of the pixel value it
 * uses (mask), how far they are shifted, and the largest value (max).
 * ch[0] = red, ch[1] = green, ch[2] = blue. */
typedef struct { unsigned long mask, max; int shift; } Chan;
static Chan ch[3];

/* work out shift and max from a mask such as 0xff0000 */
static void chan_init(Chan *c, unsigned long m)
{
    c->mask = m;
    c->shift = 0;
    while (m && !(m & 1)) { m >>= 1; c->shift++; }
    c->max = m;
}

/* 0xRRGGBB -> pixel value for this display */
static unsigned long rgb_pixel(unsigned rgb)
{
    unsigned v[3] = { (rgb >> 16) & 255, (rgb >> 8) & 255, rgb & 255 };
    unsigned long p = 0;
    for (int i = 0; i < 3; i++)
        p |= (v[i] * ch[i].max / 255) << ch[i].shift;
    return p;
}

/* pixel value -> 3 bytes R, G, B (each 0..255) */
static void pixel_rgb(unsigned long p, unsigned char *out)
{
    for (int i = 0; i < 3; i++)
        out[i] = ch[i].max ? ((p & ch[i].mask) >> ch[i].shift) * 255 / ch[i].max : 0;
}

static unsigned long pixel_half(unsigned long p) /* half brightness */
{
    unsigned long q = 0;
    for (int i = 0; i < 3; i++)
        q |= ((p & ch[i].mask) >> 1) & ch[i].mask; /* halve each channel in place */
    return q;
}

/* ---------- text ---------- */

/* text helpers; fall back to rough sizes if no font could be loaded */
static int text_w(const char *s) { return font ? XTextWidth(font, s, strlen(s)) : 6 * (int)strlen(s); }
static int font_asc(void) { return font ? font->ascent : 10; }
static int font_h(void) { return font ? font->ascent + font->descent : 13; }

/* draw s with its baseline at y, in color fg (0xRRGGBB) */
static void draw_text(Drawable d, int x, int y, const char *s, unsigned fg)
{
    XSetForeground(dpy, gc, rgb_pixel(fg));
    XDrawString(dpy, d, gc, x, y, s, strlen(s));
}

/* ---------- PNG (stb_image_write) ---------- */

/* a captured image: w*h pixels, 3 bytes (R, G, B) each, rows top to bottom */
typedef struct { int w, h; unsigned char *rgb; } Img;

/* growable byte buffer; fail is set if memory ran out */
typedef struct { unsigned char *p; size_t len, cap; int fail; } Buf;

/* stb write callback: append n bytes to the Buf in ctx */
static void buf_put(void *ctx, void *data, int n)
{
    Buf *b = ctx;
    if (b->fail || n <= 0)
        return;
    if (b->len + n > b->cap) {
        size_t cap = b->cap ? b->cap : 65536;
        while (cap < b->len + n)
            cap *= 2; /* grow by doubling */
        unsigned char *q = realloc(b->p, cap);
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

/* Encode to PNG in memory. Returns 0 on success; caller frees out->p. */
static int png_mem(const Img *im, Buf *out)
{
    memset(out, 0, sizeof *out);
    if (!stbi_write_png_to_func(buf_put, out, im->w, im->h, 3, im->rgb, im->w * 3) || out->fail) {
        free(out->p);
        out->p = NULL;
        return -1;
    }
    return 0;
}

/* write the image as PNG to stdout (-o -). 1 = ok */
static int img_stdout(const Img *im)
{
    Buf b;
    if (png_mem(im, &b)) {
        fprintf(stderr, "Could not encode the PNG\n");
        return 0;
    }
    int ok = fwrite(b.p, 1, b.len, stdout) == b.len && fflush(stdout) == 0;
    free(b.p);
    if (!ok)
        fprintf(stderr, "Could not write the PNG to stdout\n");
    null_fd(1); /* close the pipe so the reader sees EOF while we keep running */
    return ok;
}

/* <out_dir>/snappin-YYYYmmdd-HHMMSS[-N].png that does not exist yet */
static void unique_path(char *path, size_t n)
{
    char stamp[32];
    time_t t = time(NULL);
    strftime(stamp, sizeof stamp, "%Y%m%d-%H%M%S", localtime(&t));
    snprintf(path, n, "%s/snappin-%s.png", out_dir, stamp);
    /* add -2, -3, ... when several captures land in the same second */
    for (int i = 2; access(path, F_OK) == 0 && i < 1000; i++)
        snprintf(path, n, "%s/snappin-%s-%d.png", out_dir, stamp, i);
}

/* Save to the -o file the first time, then to timestamped files. 1 = ok */
static int img_save(const Img *im)
{
    char path[4200];
    if (out_file && !out_file_used) {
        out_file_used = 1;
        if (!strcmp(out_file, "-"))
            return img_stdout(im);
        snprintf(path, sizeof path, "%s", out_file);
    } else {
        unique_path(path, sizeof path);
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
 * X11 has no shared clipboard buffer. Copying means "owning" the CLIPBOARD
 * selection: when another program pastes, the X server sends us a
 * SelectionRequest and we write the data into a property on the requesting
 * window, then reply with a SelectionNotify event. So the PNG has to stay in
 * memory for as long as we own the selection.
 */

static Atom a_clipboard, a_targets, a_timestamp, a_png, a_incr, a_time;
static Window clip_win;   /* hidden window that owns the selection */
static size_t chunk_max;  /* largest property we write in one request */
/* the PNG we are serving, and the time we took ownership */
static struct { unsigned char *data; size_t len; Time time; int owned; } clip;

/* INCR transfer, for data larger than one X request: the data is sent in
 * chunks, one each time the requestor deletes the property. Each transfer keeps
 * its own copy so it can finish even if the clipboard changes meanwhile.
 * req/prop = where to write, off = bytes sent so far, last = time of the last
 * chunk (for the timeout). */
typedef struct { Window req; Atom prop; unsigned char *data; size_t len, off; long last; } Xfer;
static Xfer xfers[MAX_XFERS];
static int nxfers;

/* forget the clipboard data (we no longer own the selection) */
static void clip_drop(void)
{
    free(clip.data);
    clip.data = NULL;
    clip.len = 0;
    clip.owned = 0;
}

/* stop transfer i and remove it from the list (order does not matter) */
static void xfer_end(int i)
{
    XSelectInput(dpy, xfers[i].req, NoEventMask);
    free(xfers[i].data);
    xfers[i] = xfers[--nxfers];
}

/* Current X server time, for taking the selection without a user event.
 * Appending zero bytes to a property changes nothing but still produces a
 * PropertyNotify event, which carries the server timestamp. */
static Time server_time(void)
{
    XEvent e;
    XChangeProperty(dpy, clip_win, a_time, XA_INTEGER, 32, PropModeAppend, NULL, 0);
    XWindowEvent(dpy, clip_win, PropertyChangeMask, &e);
    return e.xproperty.time;
}

/* encode the image and take ownership of CLIPBOARD. 1 = ok */
static int clip_set(const Img *im, Time t)
{
    Buf b;
    if (png_mem(im, &b))
        return 0;
    free(clip.data);
    clip.data = b.p;
    clip.len = b.len;
    clip.time = t;
    XSetSelectionOwner(dpy, a_clipboard, clip_win, t);
    clip.owned = XGetSelectionOwner(dpy, a_clipboard) == clip_win; /* check it really worked */
    if (!clip.owned)
        clip_drop();
    return clip.owned;
}

/* Answer a paste request. Supported targets: TARGETS (list of formats we offer),
 * TIMESTAMP and image/png. Anything else is refused (property = None). */
static void clip_request(XSelectionRequestEvent *r)
{
    XSelectionEvent ev = { 0 };
    ev.type = SelectionNotify;
    ev.display = r->display;
    ev.requestor = r->requestor;
    ev.selection = r->selection;
    ev.target = r->target;
    ev.time = r->time;
    ev.property = None;
    Atom prop = r->property != None ? r->property : r->target; /* obsolete clients */

    if (clip.owned && r->selection == a_clipboard) {
        if (r->target == a_targets) {
            Atom t[] = { a_targets, a_timestamp, a_png };
            XChangeProperty(dpy, r->requestor, prop, XA_ATOM, 32, PropModeReplace, (unsigned char *)t, 3);
            ev.property = prop;
        } else if (r->target == a_timestamp) {
            long v = (long)clip.time;
            XChangeProperty(dpy, r->requestor, prop, XA_INTEGER, 32, PropModeReplace, (unsigned char *)&v, 1);
            ev.property = prop;
        } else if (r->target == a_png) {
            if (clip.len <= chunk_max) { /* small enough: send it all at once */
                XChangeProperty(dpy, r->requestor, prop, a_png, 8, PropModeReplace, clip.data, (int)clip.len);
                ev.property = prop;
            } else if (nxfers < MAX_XFERS) { /* too big: start an INCR transfer */
                Xfer *x = &xfers[nxfers];
                x->data = malloc(clip.len);
                if (x->data) {
                    memcpy(x->data, clip.data, clip.len);
                    x->req = r->requestor;
                    x->prop = prop;
                    x->len = clip.len;
                    x->off = 0;
                    x->last = now_ms();
                    nxfers++;
                    /* the requestor deletes the property to ask for the next chunk */
                    XSelectInput(dpy, r->requestor, PropertyChangeMask);
                    /* writing an INCR property (holding the total size) starts the transfer */
                    long size = (long)clip.len;
                    XChangeProperty(dpy, r->requestor, prop, a_incr, 32, PropModeReplace, (unsigned char *)&size, 1);
                    ev.property = prop;
                }
            }
        }
    }
    /* tell the requestor we are done (property = None means refused) */
    XSendEvent(dpy, r->requestor, False, NoEventMask, (XEvent *)&ev);
}

/* A property was deleted: if it belongs to an INCR transfer, the requestor has
 * read the last chunk, so send the next one. Returns 1 if the event was ours. */
static int xfer_event(XPropertyEvent *e)
{
    if (e->state != PropertyDelete)
        return 0;
    for (int i = 0; i < nxfers; i++) {
        Xfer *x = &xfers[i];
        if (x->req != e->window || x->prop != e->atom)
            continue;
        size_t n = x->len - x->off < chunk_max ? x->len - x->off : chunk_max;
        XChangeProperty(dpy, x->req, x->prop, a_png, 8, PropModeReplace, x->data + x->off, (int)n);
        x->off += n;
        x->last = now_ms();
        if (n == 0) /* a zero-length chunk ends the transfer */
            xfer_end(i);
        return 1;
    }
    return 0;
}

/* ---------- pins ---------- */

/* a floating window showing one capture */
typedef struct {
    Window win;
    Pixmap pm;              /* the image drawn at the current scale */
    Img img;                /* original pixels (copy/save always use these) */
    int x, y, w, h, dx, dy; /* window position and size; dx/dy = grab offset while dragging */
    double scale, alpha;    /* zoom factor, opacity */
    unsigned long border;   /* current border color (changes while flashing) */
    long flash_end;         /* when the flash ends (ms), 0 = not flashing */
    Time last_click;        /* for double click detection */
} Pin;

static Pin *pins[MAX_PINS];
static int npins;

static void menu_close(void);
/* the right click menu (at most one open): which pin it belongs to, the
 * highlighted item, width, item height and when it was opened */
static struct { Window win; Pin *pin; int sel, w, ih; Time opened; } menu;

/* the pin that owns window w, or NULL */
static Pin *pin_find(Window w)
{
    for (int i = 0; i < npins; i++)
        if (pins[i]->win == w)
            return pins[i];
    return NULL;
}

/* copy the pixmap to the window and draw a 1 px border */
static void pin_draw(Pin *p)
{
    XCopyArea(dpy, p->pm, p->win, gc, 0, 0, p->w, p->h, 0, 0);
    XSetForeground(dpy, gc, p->border);
    XDrawRectangle(dpy, p->win, gc, 0, 0, p->w - 1, p->h - 1);
}

/* Rebuild the pixmap at the current scale (bilinear) and resize the window.
 * Fixed point math: positions are in 1/256 pixel units, so fx >> 8 is the
 * source pixel and fx & 255 is the weight of its right neighbour. */
static void pin_render(Pin *p)
{
    const Img *s = &p->img;
    int w = iround(s->w * p->scale), h = iround(s->h * p->scale);
    if (w < 1) w = 1;
    if (h < 1) h = 1;
    XImage *xi = XCreateImage(dpy, vis, depth, ZPixmap, 0, NULL, w, h, 32, 0);
    xi->data = malloc((size_t)xi->bytes_per_line * h);
    for (int y = 0; y < h; y++) {
        /* center of output row y mapped into the source, minus half a pixel */
        long fy = (long)(2 * y + 1) * s->h * 128 / h - 128;
        if (fy < 0) fy = 0;
        int y0 = fy >> 8, ty = fy & 255, y1 = y0 + 1 < s->h ? y0 + 1 : y0;
        for (int x = 0; x < w; x++) {
            long fx = (long)(2 * x + 1) * s->w * 128 / w - 128;
            if (fx < 0) fx = 0;
            int x0 = fx >> 8, tx = fx & 255, x1 = x0 + 1 < s->w ? x0 + 1 : x0;
            /* the 4 source pixels around the point: a b / c d */
            const unsigned char *a = s->rgb + ((size_t)y0 * s->w + x0) * 3,
                                *b = s->rgb + ((size_t)y0 * s->w + x1) * 3,
                                *c = s->rgb + ((size_t)y1 * s->w + x0) * 3,
                                *d = s->rgb + ((size_t)y1 * s->w + x1) * 3;
            unsigned v = 0;
            for (int i = 0; i < 3; i++) {
                unsigned top = a[i] * (256 - tx) + b[i] * tx, bot = c[i] * (256 - tx) + d[i] * tx;
                v = v << 8 | ((top * (256 - ty) + bot * ty) >> 16); /* /256/256 */
            }
            XPutPixel(xi, x, y, rgb_pixel(v));
        }
    }
    if (p->pm)
        XFreePixmap(dpy, p->pm);
    p->pm = XCreatePixmap(dpy, root, w, h, depth);
    XPutImage(dpy, p->pm, gc, xi, 0, 0, 0, 0, w, h);
    XDestroyImage(xi);
    p->w = w;
    p->h = h;
    XMoveResizeWindow(dpy, p->win, p->x, p->y, w, h);
    pin_draw(p);
}

/* create a floating window for img at screen position x, y; takes ownership of img */
static void pin_new(Img img, int x, int y)
{
    if (npins == MAX_PINS) {
        free(img.rgb);
        return;
    }
    Pin *p = calloc(1, sizeof *p);
    p->img = img;
    p->x = x;
    p->y = y;
    p->scale = p->alpha = 1.0;
    p->border = border_px;

    XSetWindowAttributes a = { 0 };
    a.override_redirect = True; /* no window manager frame, stays exactly where we put it */
    a.background_pixmap = None; /* do not clear before redraw, avoids flicker */
    a.cursor = cur_move;
    a.event_mask = ExposureMask | ButtonPressMask | ButtonReleaseMask | Button1MotionMask |
                   KeyPressMask | EnterWindowMask;
    p->win = XCreateWindow(dpy, root, x, y, img.w, img.h, 0, CopyFromParent, InputOutput,
                           CopyFromParent, CWOverrideRedirect | CWBackPixmap | CWCursor | CWEventMask, &a);
    XStoreName(dpy, p->win, "snappin");
    XClassHint cls = { "snappin", "Snappin" };
    XSetClassHint(dpy, p->win, &cls);
    pins[npins++] = p;
    pin_render(p);
    XMapRaised(dpy, p->win);
}

/* destroy a pin and free everything it holds */
static void pin_close(Pin *p)
{
    if (menu.win && menu.pin == p)
        menu_close();
    for (int i = 0; i < npins; i++)
        if (pins[i] == p) {
            pins[i] = pins[--npins];
            break;
        }
    XDestroyWindow(dpy, p->win);
    XFreePixmap(dpy, p->pm);
    free(p->img.rgb);
    free(p);
}

/* multiply the zoom by f around the screen point rx, ry (limits: 0.1x .. 8x) */
static void pin_zoom(Pin *p, int rx, int ry, double f)
{
    double s = p->scale * f;
    if (s < 0.1) s = 0.1;
    if (s > 8.0) s = 8.0;
    if (s > 0.999 && s < 1.001) s = 1.0; /* snap to exactly 1x after rounding errors */
    if (s == p->scale || (double)p->img.w * s * p->img.h * s > MAX_PIXELS)
        return;
    /* keep the point under the mouse in place */
    double k = s / p->scale;
    p->x = iround(rx - (rx - p->x) * k);
    p->y = iround(ry - (ry - p->y) * k);
    p->scale = s;
    pin_render(p);
}

/* back to 1x (key 1) */
static void pin_reset(Pin *p)
{
    p->scale = 1.0;
    pin_render(p);
}

/* change opacity by step (0.2 .. 1.0) */
static void pin_fade(Pin *p, double step)
{
    /* opacity is only visible with a compositor running */
    p->alpha += step;
    if (p->alpha < 0.2) p->alpha = 0.2;
    if (p->alpha > 0.999) p->alpha = 1.0;
    if (p->alpha == 1.0) {
        XDeleteProperty(dpy, p->win, a_opacity);
    } else {
        /* 32-bit properties are passed as long in Xlib; 0xffffffff = fully opaque */
        unsigned long v = (unsigned long)(p->alpha * 0xffffffffUL);
        XChangeProperty(dpy, p->win, a_opacity, XA_CARDINAL, 32, PropModeReplace, (unsigned char *)&v, 1);
    }
}

/* briefly color the border (green = ok, red = failed); the main loop restores it */
static void pin_flash(Pin *p, unsigned rgb)
{
    p->border = rgb_pixel(rgb);
    p->flash_end = now_ms() + FLASH_MS;
    pin_draw(p);
}

/* copy to the clipboard and report it. t = time of the user event (or server time) */
static int img_copy(const Img *im, Time t)
{
    int ok = clip_set(im, t);
    if (ok)
        info("Copied %dx%d PNG to the clipboard (image/png)\n", im->w, im->h);
    else
        fprintf(stderr, "Could not take the clipboard\n");
    return ok;
}

static void pin_copy(Pin *p, Time t) { pin_flash(p, img_copy(&p->img, t) ? 0x00ff00 : 0xff0000); }

static void pin_save(Pin *p) { pin_flash(p, img_save(&p->img) ? 0x00ff00 : 0xff0000); }

/* a new capture is ready: save / copy / pin it as the options say */
static void deliver(Img im, int x, int y)
{
    int ok = 1;
    captured++;
    if (!opt.nosave && !img_save(&im))
        ok = 0;
    if (opt.clipboard && !img_copy(&im, server_time()))
        ok = 0;
    if (!ok)
        exit_code = 1;
    if (opt.pin)
        pin_new(im, x, y);
    else
        free(im.rgb);
}

static void new_capture(void) { capture_at = now_ms() + 200; } /* capture after the menu is gone */

/* close every pin (menu: Close all) */
static void close_all(void)
{
    while (npins)
        pin_close(pins[0]);
}

/* ---------- right click menu ---------- */

/* menu items and their shortcut labels; the order matches menu_event() */
static const char *menu_label[] = { "Copy", "Save", "Actual size", "New capture", "Close", "Close all" };
static const char *menu_key[] = { "Ctrl+C", "Ctrl+S", "1", "N", "Esc", "" };
#define MENU_N 6

/* draw all items, the highlighted one with the border color */
static void menu_draw(void)
{
    XSetForeground(dpy, gc, rgb_pixel(0x2b2b2b));
    XFillRectangle(dpy, menu.win, gc, 0, 0, menu.w, menu.ih * MENU_N);
    for (int i = 0; i < MENU_N; i++) {
        int y = i * menu.ih, base = y + (menu.ih - font_h()) / 2 + font_asc();
        unsigned fg = 0xeeeeee;
        if (i == menu.sel) {
            XSetForeground(dpy, gc, border_px);
            XFillRectangle(dpy, menu.win, gc, 0, y, menu.w, menu.ih);
            fg = 0x000000;
        }
        draw_text(menu.win, 12, base, menu_label[i], fg);
        draw_text(menu.win, menu.w - 12 - text_w(menu_key[i]), base, menu_key[i], i == menu.sel ? fg : 0x999999);
    }
    XSetForeground(dpy, gc, rgb_pixel(0x555555));
    XDrawRectangle(dpy, menu.win, gc, 0, 0, menu.w - 1, menu.ih * MENU_N - 1);
}

/* open the menu for pin p at screen position rx, ry */
static void menu_open(Pin *p, int rx, int ry, Time t)
{
    int lw = 0, kw = 0;
    for (int i = 0; i < MENU_N; i++) {
        if (text_w(menu_label[i]) > lw) lw = text_w(menu_label[i]);
        if (text_w(menu_key[i]) > kw) kw = text_w(menu_key[i]);
    }
    menu.w = lw + kw + 48;
    menu.ih = font_h() + 10;
    menu.sel = -1;
    menu.pin = p;
    menu.opened = t;
    int h = menu.ih * MENU_N;
    /* keep the menu on screen */
    if (rx + menu.w > SW) rx = SW - menu.w;
    if (ry + h > SH) ry = SH - h;

    XSetWindowAttributes a = { 0 };
    a.override_redirect = True;
    a.background_pixmap = None;
    a.event_mask = ExposureMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | KeyPressMask;
    menu.win = XCreateWindow(dpy, root, rx, ry, menu.w, h, 0, CopyFromParent, InputOutput,
                             CopyFromParent, CWOverrideRedirect | CWBackPixmap | CWEventMask, &a);
    XMapRaised(dpy, menu.win);
    XSync(dpy, False);
    /* grab input so a click anywhere else closes the menu */
    XGrabPointer(dpy, menu.win, False, ButtonPressMask | ButtonReleaseMask | PointerMotionMask,
                 GrabModeAsync, GrabModeAsync, None, None, CurrentTime);
    XGrabKeyboard(dpy, menu.win, False, GrabModeAsync, GrabModeAsync, CurrentTime);
    menu_draw();
}

static void menu_close(void)
{
    XUngrabPointer(dpy, CurrentTime);
    XUngrabKeyboard(dpy, CurrentTime);
    XDestroyWindow(dpy, menu.win);
    menu.win = 0;
}

/* index of the item at x, y (menu coordinates), or -1 */
static int menu_hit(int x, int y)
{
    return x >= 0 && x < menu.w && y >= 0 && y < menu.ih * MENU_N ? y / menu.ih : -1;
}

/* events for the menu window: hover highlights, release on an item runs it */
static void menu_event(XEvent *e)
{
    switch (e->type) {
    case Expose:
        if (e->xexpose.count == 0)
            menu_draw();
        break;
    case MotionNotify: {
        int s = menu_hit(e->xmotion.x, e->xmotion.y);
        if (s != menu.sel) {
            menu.sel = s;
            menu_draw();
        }
        break;
    }
    case ButtonPress:
        if (menu_hit(e->xbutton.x, e->xbutton.y) < 0)
            menu_close(); /* clicked outside */
        break;
    case ButtonRelease: {
        int s = menu_hit(e->xbutton.x, e->xbutton.y);
        if (s < 0 || e->xbutton.time - menu.opened < 250) /* ignore release of the opening click */
            break;
        Pin *p = menu.pin;
        menu_close();
        switch (s) {
        case 0: pin_copy(p, e->xbutton.time); break;
        case 1: pin_save(p); break;
        case 2: pin_reset(p); break;
        case 3: new_capture(); break;
        case 4: pin_close(p); break;
        case 5: close_all(); break;
        }
        break;
    }
    case KeyPress:
        if (XLookupKeysym(&e->xkey, 0) == XK_Escape)
            menu_close();
        break;
    }
}

/* events for a pin window: mouse and keyboard controls */
static void pin_event(Pin *p, XEvent *e)
{
    switch (e->type) {
    case Expose:
        if (e->xexpose.count == 0)
            pin_draw(p);
        break;
    case EnterNotify:
        /* override-redirect windows never get focus from the WM, so take it on hover */
        XSetInputFocus(dpy, p->win, RevertToPointerRoot, CurrentTime);
        break;
    case ButtonPress: {
        XButtonEvent *b = &e->xbutton;
        int ctrl = b->state & ControlMask;
        if (b->button == Button1) {
            if (b->time - p->last_click < DCLICK_MS) {
                pin_close(p);
                return;
            }
            p->last_click = b->time;
            /* remember where inside the window we grabbed it, for dragging */
            p->dx = b->x_root - p->x;
            p->dy = b->y_root - p->y;
            XRaiseWindow(dpy, p->win);
        } else if (b->button == Button3) {
            menu_open(p, b->x_root, b->y_root, b->time);
        } else if (b->button == Button4) { /* wheel up */
            if (ctrl) pin_fade(p, 0.1);
            else pin_zoom(p, b->x_root, b->y_root, 1.1);
        } else if (b->button == Button5) { /* wheel down */
            if (ctrl) pin_fade(p, -0.1);
            else pin_zoom(p, b->x_root, b->y_root, 1 / 1.1);
        }
        break;
    }
    case MotionNotify: /* only arrives while button 1 is held (Button1MotionMask) */
        while (XCheckTypedWindowEvent(dpy, p->win, MotionNotify, e))
            ; /* use only the latest position */
        p->x = e->xmotion.x_root - p->dx;
        p->y = e->xmotion.y_root - p->dy;
        XMoveWindow(dpy, p->win, p->x, p->y);
        break;
    case KeyPress: {
        KeySym k = XLookupKeysym(&e->xkey, 0); /* index 0 = ignore Shift, so 'c' not 'C' */
        int ctrl = e->xkey.state & ControlMask;
        if (k == XK_Escape) pin_close(p);
        else if (ctrl && k == XK_c) pin_copy(p, e->xkey.time);
        else if (ctrl && k == XK_s) pin_save(p);
        else if (!ctrl && k == XK_1) pin_reset(p);
        else if (!ctrl && k == XK_n) new_capture();
        break;
    }
    }
}

/* ---------- area selection ----------
 *
 * The whole screen is grabbed once, then shown frozen and darkened in a
 * fullscreen window. The selected box is drawn from the original bright copy.
 * The final image is cut from the same frozen shot, so what you see while
 * selecting is exactly what you get.
 */

static struct {
    int active, pressing, box; /* selecting now / button held / box is non-empty */
    int sx, sy;                /* where the drag started */
    int x0, y0, x1, y1;        /* current box, x0 <= x1, y0 <= y1 (x1, y1 exclusive) */
    Window win;                /* fullscreen selection window */
    Pixmap orig, dark, back;   /* bright screen, darkened screen, back buffer */
    XImage *shot;              /* the frozen screen pixels */
} sel;

/* redraw: dark screen, bright box, frame and a "W x H" label, via the back
 * buffer so it does not flicker */
static void sel_draw(void)
{
    XCopyArea(dpy, sel.dark, sel.back, gc, 0, 0, SW, SH, 0, 0);
    if (sel.box) {
        int w = sel.x1 - sel.x0, h = sel.y1 - sel.y0;
        char t[32];
        XCopyArea(dpy, sel.orig, sel.back, gc, sel.x0, sel.y0, w, h, sel.x0, sel.y0);
        XSetForeground(dpy, gc, border_px);
        XDrawRectangle(dpy, sel.back, gc, sel.x0 - 1, sel.y0 - 1, w + 1, h + 1);
        snprintf(t, sizeof t, "%d x %d", w, h);
        /* label above the box, or below it if there is no room */
        int ly = sel.y0 > font_h() + 8 ? sel.y0 - 6 : sel.y1 + font_asc() + 6;
        draw_text(sel.back, sel.x0 + 1, ly + 1, t, 0x000000); /* shadow */
        draw_text(sel.back, sel.x0, ly, t, 0xffffff);
    }
    XCopyArea(dpy, sel.back, sel.win, gc, 0, 0, SW, SH, 0, 0);
}

/* copy a w*h area at x0, y0 of an XImage into a new RGB Img */
static Img img_from(XImage *xi, int x0, int y0, int w, int h)
{
    Img im = { w, h, malloc((size_t)w * h * 3) };
    for (int y = 0; y < h; y++)
        for (int x = 0; x < w; x++)
            pixel_rgb(XGetPixel(xi, x0 + x, y0 + y), im.rgb + ((size_t)y * w + x) * 3);
    return im;
}

/* freeze the screen and show the selection window */
static void start_capture(void)
{
    if (sel.active)
        return;
    XImage *shot = XGetImage(dpy, root, 0, 0, SW, SH, AllPlanes, ZPixmap);
    if (!shot) {
        fprintf(stderr, "Could not grab the screen. Is this an X11 session?\n");
        exit_code = 1;
        return;
    }
    /* darkened copy */
    size_t n = (size_t)shot->bytes_per_line * SH;
    char *d = malloc(n);
    memcpy(d, shot->data, n);
    XImage *dark = XCreateImage(dpy, vis, shot->depth, ZPixmap, 0, d, SW, SH, shot->bitmap_pad, shot->bytes_per_line);
    uint16_t one = 1;
    int host_lsb = *(unsigned char *)&one == 1;
    /* fast path: 32-bit pixels in host byte order can be edited directly;
     * otherwise use the slow but general XGetPixel/XPutPixel */
    if (dark->bits_per_pixel == 32 && (dark->byte_order == LSBFirst) == host_lsb) {
        for (int y = 0; y < SH; y++) {
            uint32_t *row = (uint32_t *)(dark->data + (size_t)y * dark->bytes_per_line);
            for (int x = 0; x < SW; x++)
                row[x] = pixel_half(row[x]);
        }
    } else {
        for (int y = 0; y < SH; y++)
            for (int x = 0; x < SW; x++)
                XPutPixel(dark, x, y, pixel_half(XGetPixel(dark, x, y)));
    }

    /* upload both versions to the server once; redraws are then cheap copies */
    sel.orig = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.dark = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.back = XCreatePixmap(dpy, root, SW, SH, depth);
    XPutImage(dpy, sel.orig, gc, shot, 0, 0, 0, 0, SW, SH);
    XPutImage(dpy, sel.dark, gc, dark, 0, 0, 0, 0, SW, SH);
    XDestroyImage(dark);
    sel.shot = shot;

    XSetWindowAttributes a = { 0 };
    a.override_redirect = True;
    a.background_pixmap = sel.dark; /* shown at once, before the first redraw */
    a.cursor = cur_cross;
    a.event_mask = ExposureMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | KeyPressMask;
    sel.win = XCreateWindow(dpy, root, 0, 0, SW, SH, 0, CopyFromParent, InputOutput, CopyFromParent,
                            CWOverrideRedirect | CWBackPixmap | CWCursor | CWEventMask, &a);
    XMapRaised(dpy, sel.win);
    XSync(dpy, False);
    sel.active = 1;
    sel.pressing = sel.box = 0;

    /* grab keyboard and pointer; retry for up to 1 s because the key or menu
     * that started us may still hold a grab */
    for (int i = 0; i < 40; i++) {
        if (XGrabPointer(dpy, sel.win, False, ButtonPressMask | ButtonReleaseMask | PointerMotionMask,
                         GrabModeAsync, GrabModeAsync, None, cur_cross, CurrentTime) == GrabSuccess)
            break;
        usleep(25000);
    }
    for (int i = 0; i < 40; i++) {
        if (XGrabKeyboard(dpy, sel.win, False, GrabModeAsync, GrabModeAsync, CurrentTime) == GrabSuccess)
            break;
        usleep(25000);
    }
    sel_draw();
}

/* close the selection screen; take = 1 delivers the box, 0 cancels */
static void sel_finish(int take)
{
    XUngrabPointer(dpy, CurrentTime);
    XUngrabKeyboard(dpy, CurrentTime);
    XDestroyWindow(dpy, sel.win);
    XFreePixmap(dpy, sel.orig);
    XFreePixmap(dpy, sel.dark);
    XFreePixmap(dpy, sel.back);
    sel.active = 0;
    if (take) {
        int w = sel.x1 - sel.x0, h = sel.y1 - sel.y0;
        deliver(img_from(sel.shot, sel.x0, sel.y0, w, h), sel.x0, sel.y0);
    } else {
        info("Cancelled\n");
        if (!captured)
            exit_code = 1; /* cancelling the very first capture is a failure */
    }
    XDestroyImage(sel.shot);
}

/* capture a fixed area without the selection screen */
static void grab_rect(int x, int y, int w, int h)
{
    XImage *xi = XGetImage(dpy, root, x, y, w, h, AllPlanes, ZPixmap);
    if (!xi) {
        fprintf(stderr, "Could not grab the screen. Is this an X11 session?\n");
        exit_code = 1;
        return;
    }
    deliver(img_from(xi, 0, 0, w, h), x, y);
    XDestroyImage(xi);
}

/* the pointer is at x, y: update the box between it and the start point */
static void sel_update(int x, int y)
{
    if (x < 0) x = 0;
    if (y < 0) y = 0;
    if (x > SW) x = SW;
    if (y > SH) y = SH;
    sel.x0 = x < sel.sx ? x : sel.sx;
    sel.x1 = x < sel.sx ? sel.sx : x;
    sel.y0 = y < sel.sy ? y : sel.sy;
    sel.y1 = y < sel.sy ? sel.sy : y;
    sel.box = sel.x1 > sel.x0 && sel.y1 > sel.y0;
}

/* events for the selection window */
static void sel_event(XEvent *e)
{
    switch (e->type) {
    case Expose:
        if (e->xexpose.count == 0)
            sel_draw();
        break;
    case ButtonPress:
        if (e->xbutton.button == Button3) {
            sel_finish(0);
        } else if (e->xbutton.button == Button1) {
            sel.sx = e->xbutton.x < 0 ? 0 : e->xbutton.x > SW ? SW : e->xbutton.x;
            sel.sy = e->xbutton.y < 0 ? 0 : e->xbutton.y > SH ? SH : e->xbutton.y;
            sel.pressing = 1;
            sel.box = 0;
            sel_draw();
        }
        break;
    case MotionNotify:
        if (!sel.pressing)
            break;
        while (XCheckTypedWindowEvent(dpy, sel.win, MotionNotify, e))
            ; /* use only the latest position */
        sel_update(e->xmotion.x, e->xmotion.y);
        sel_draw();
        break;
    case ButtonRelease:
        if (e->xbutton.button != Button1 || !sel.pressing)
            break;
        sel_update(e->xbutton.x, e->xbutton.y);
        sel.pressing = 0;
        if (sel.box && sel.x1 - sel.x0 >= 3 && sel.y1 - sel.y0 >= 3) {
            sel_finish(1);
        } else { /* too small: let the user select again */
            sel.box = 0;
            sel_draw();
        }
        break;
    case KeyPress:
        if (XLookupKeysym(&e->xkey, 0) == XK_Escape)
            sel_finish(0);
        break;
    }
}

/* ---------- main ---------- */

static int on_xerror(Display *d, XErrorEvent *e)
{
    (void)d; (void)e; /* ignore errors such as requests on already destroyed windows */
    return 0;
}

/* --help text */
static void usage(FILE *f)
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
"Pin window: drag = move, wheel = zoom, Ctrl+wheel = opacity,\n"
"  Ctrl+C = copy, Ctrl+S = save (to the -o place), 1 = actual size,\n"
"  N = new capture, double click / Esc = close, right click = menu\n"
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
"  snappin -o - | convert - out.jpg    PNG to stdout\n", f);
}

/* print a usage error and return exit status 2 */
static int bad_usage(const char *msg, const char *arg)
{
    fprintf(stderr, "snappin: %s%s%s\nTry 'snappin --help'.\n", msg, arg ? ": " : "", arg ? arg : "");
    return 2;
}

/* Fill out_dir / out_file from -o:
 *   none      -> timestamped files in .
 *   -         -> stdout
 *   dir/ or an existing directory -> timestamped files there (created if needed)
 *   anything else -> that file name; later saves (Ctrl+S) go next to it
 * Returns 0 = ok, otherwise an exit status. */
static int setup_output(void)
{
    const char *o = opt.output;
    struct stat st;
    if (!o) {
        strcpy(out_dir, ".");
        return 0;
    }
    if (!*o)
        return bad_usage("empty --output", NULL);
    if (!strcmp(o, "-")) {
        out_file = o;
        strcpy(out_dir, ".");
        return 0;
    }
    size_t n = strlen(o);
    if (n >= sizeof out_dir)
        return bad_usage("--output path too long", NULL);
    if (o[n - 1] == '/' || (stat(o, &st) == 0 && S_ISDIR(st.st_mode))) {
        strcpy(out_dir, o);
        while (n > 1 && out_dir[n - 1] == '/') /* strip trailing slashes, keep "/" */
            out_dir[--n] = 0;
        if (mkdir(out_dir, 0755) && errno != EEXIST) {
            fprintf(stderr, "snappin: cannot create directory: %s\n", out_dir);
            return 1;
        }
        return 0;
    }
    out_file = o;
    /* out_dir = the directory part of the file name */
    strcpy(out_dir, o);
    char *s = strrchr(out_dir, '/');
    if (!s)
        strcpy(out_dir, ".");
    else if (s == out_dir)
        s[1] = 0;
    else
        *s = 0;
    return 0;
}

int main(int argc, char **argv)
{
    static const struct option longopts[] = {
        { "geometry", required_argument, 0, 'g' },
        { "fullscreen", no_argument, 0, 'f' },
        { "output", required_argument, 0, 'o' },
        { "no-save", no_argument, 0, 'n' },
        { "clipboard", no_argument, 0, 'c' },
        { "pin", no_argument, 0, 'p' },
        { "delay", required_argument, 0, 'd' },
        { "quiet", no_argument, 0, 'q' },
        { "help", no_argument, 0, 'h' },
        { "version", no_argument, 0, 'V' },
        { 0, 0, 0, 0 }
    };
    /* parse options */
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
        case 'd':
            opt.delay = strtod(optarg, &end);
            if (end == optarg || *end || opt.delay < 0 || opt.delay > 86400)
                return bad_usage("bad --delay", optarg);
            break;
        case 'q': opt.quiet = 1; break;
        case 'h': usage(stdout); return 0;
        case 'V': puts("snappin " VERSION); return 0;
        default: return 2; /* getopt already printed the error */
        }
    }
    if (optind < argc)
        return bad_usage("unexpected argument", argv[optind]);
    if (opt.geometry && opt.full)
        return bad_usage("use only one of --geometry and --fullscreen", NULL);
    if (opt.nosave && !opt.clipboard && !opt.pin)
        return bad_usage("--no-save needs --clipboard or --pin, or there is nothing to do", NULL);
    int r = setup_output();
    if (r)
        return r;

    /* a closed pipe on stdout (-o -) should be an error we report, not a crash */
    signal(SIGPIPE, SIG_IGN);
    dpy = XOpenDisplay(NULL);
    if (!dpy) {
        fprintf(stderr, "Cannot open the X11 display (DISPLAY). Run this in an X11 session.\n");
        return 1;
    }
    XSetErrorHandler(on_xerror);
    /* screen and color format */
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
    chan_init(&ch[0], vis->red_mask);
    chan_init(&ch[1], vis->green_mask);
    chan_init(&ch[2], vis->blue_mask);
    border_px = rgb_pixel(BORDER_RGB);

    /* drawing resources: one GC for everything, a small fixed font, cursors */
    gc = XCreateGC(dpy, root, 0, NULL);
    font = XLoadQueryFont(dpy, "-misc-fixed-bold-r-normal--13-*-*-*-*-*-iso8859-1");
    if (!font)
        font = XLoadQueryFont(dpy, "fixed");
    if (font)
        XSetFont(dpy, gc, font->fid);
    a_opacity = XInternAtom(dpy, "_NET_WM_WINDOW_OPACITY", False);
    cur_cross = XCreateFontCursor(dpy, XC_crosshair);
    cur_move = XCreateFontCursor(dpy, XC_fleur);

    /* clipboard setup: atoms, a hidden owner window, and the chunk size
     * (max request size is in 4-byte units; leave room for the header) */
    a_clipboard = XInternAtom(dpy, "CLIPBOARD", False);
    a_targets = XInternAtom(dpy, "TARGETS", False);
    a_timestamp = XInternAtom(dpy, "TIMESTAMP", False);
    a_png = XInternAtom(dpy, "image/png", False);
    a_incr = XInternAtom(dpy, "INCR", False);
    a_time = XInternAtom(dpy, "_SNAPPIN_TIME", False);
    clip_win = XCreateSimpleWindow(dpy, root, -10, -10, 1, 1, 0, 0, 0);
    XSelectInput(dpy, clip_win, PropertyChangeMask);
    chunk_max = (size_t)XMaxRequestSize(dpy) * 4 - 1024;
    if (chunk_max > 256 * 1024)
        chunk_max = 256 * 1024;

    /* fixed area from -g / -f, clipped to the screen */
    int gx = 0, gy = 0, gw = SW, gh = SH;
    if (opt.geometry) {
        unsigned w = 0, h = 0;
        int m = XParseGeometry(opt.geometry, &gx, &gy, &w, &h);
        if (!(m & WidthValue) || !(m & HeightValue) || !w || !h)
            return bad_usage("bad --geometry (want WxH+X+Y)", opt.geometry);
        /* cap huge sizes first so the int math below cannot overflow */
        gw = w > (unsigned)SW * 2 ? SW * 2 : (int)w;
        gh = h > (unsigned)SH * 2 ? SH * 2 : (int)h;
        if (m & XNegative) gx += SW - gw;
        if (m & YNegative) gy += SH - gh;
        if (gx < 0) { gw += gx; gx = 0; }
        if (gy < 0) { gh += gy; gy = 0; }
        if (gx + gw > SW) gw = SW - gx;
        if (gy + gh > SH) gh = SH - gy;
        if (gw < 1 || gh < 1) {
            fprintf(stderr, "snappin: --geometry is outside the %dx%d screen\n", SW, SH);
            return 1;
        }
    }

    /* --delay; nanosleep may be interrupted, so continue with the remaining time */
    if (opt.delay > 0) {
        struct timespec ts = { (time_t)opt.delay, (long)((opt.delay - (time_t)opt.delay) * 1e9) };
        while (nanosleep(&ts, &ts) && errno == EINTR)
            ;
    }
    /* first capture: fixed area right away, or the interactive selection */
    if (opt.geometry || opt.full)
        grab_rect(gx, gy, gw, gh);
    else
        start_capture();

    /* Main loop: handle all queued X events, then run timers (new capture,
     * border flashes, INCR timeouts), then sleep in select() until the next X
     * event or timer. Exits when nothing is left to do. */
    int fd = ConnectionNumber(dpy), daemonized = 0;
    for (;;) {
        while (XPending(dpy)) {
            XEvent e;
            Pin *p;
            XNextEvent(dpy, &e);
            /* clipboard events first, then route by window */
            if (e.type == SelectionRequest)
                clip_request(&e.xselectionrequest);
            else if (e.type == SelectionClear) {
                if (e.xselectionclear.selection == a_clipboard)
                    clip_drop(); /* someone else copied something */
            } else if (e.type == PropertyNotify && xfer_event(&e.xproperty))
                ;
            else if (sel.active && e.xany.window == sel.win)
                sel_event(&e);
            else if (menu.win && e.xany.window == menu.win)
                menu_event(&e);
            else if ((p = pin_find(e.xany.window)))
                pin_event(p, &e);
        }

        /* timers; wait = ms until the next one, -1 = none */
        long t = now_ms(), wait = -1;
        if (capture_at) {
            if (t >= capture_at) {
                capture_at = 0;
                start_capture();
                continue;
            }
            wait = capture_at - t;
        }
        for (int i = 0; i < npins; i++) {
            Pin *p = pins[i];
            if (!p->flash_end)
                continue;
            if (t >= p->flash_end) {
                p->flash_end = 0;
                p->border = border_px;
                pin_draw(p);
            } else if (wait < 0 || p->flash_end - t < wait) {
                wait = p->flash_end - t;
            }
        }
        for (int i = nxfers - 1; i >= 0; i--) {
            long left = xfers[i].last + XFER_TIMEOUT_MS - t;
            if (left <= 0)
                xfer_end(i); /* the requestor went away */
            else if (wait < 0 || left < wait)
                wait = left;
        }
        if (!npins && !sel.active && !capture_at) {
            /* all pins are closed */
            if (!clip.owned && !nxfers)
                break; /* nothing to serve: done */
            if (!daemonized) {
                /* keep serving the clipboard in the background, like xclip does */
                daemonized = 1;
                info("Clipboard is kept by a background process until something else is copied.\n");
                fflush(stdout);
                XSync(dpy, False);
                pid_t pid = fork();
                if (pid > 0)
                    _exit(exit_code); /* parent returns to the shell; the child keeps the X connection */
                if (pid == 0) {
                    setsid(); /* leave the terminal's session so closing it does not kill us */
                    /* let $(snappin ...) and pipes finish */
                    null_fd(0);
                    null_fd(1);
                    null_fd(2);
                }
            }
        }
        if (XPending(dpy))
            continue;

        fd_set fds;
        FD_ZERO(&fds);
        FD_SET(fd, &fds);
        /* sleep until X has data or the next timer is due */
        struct timeval tv = { wait / 1000, (wait % 1000) * 1000 };
        select(fd + 1, &fds, NULL, NULL, wait >= 0 ? &tv : NULL);
    }
    XCloseDisplay(dpy);
    return exit_code;
}
