/* snappin.c — X11에서 드래그로 화면 일부를 찍고, 찍은 그림을 같은 자리에 떠 있게(핀) 띄운다.
 * snappin.py 를 C로 옮긴 것. Xlib 만 쓴다(PNG 저장은 직접 만든 간단한 인코더로).
 *
 * 빌드: cc -O2 -o snappin snappin.c -lX11
 *   Debian/Ubuntu: sudo apt install build-essential libx11-dev xclip
 * 실행: ./snappin   (단축키에 연결해 두면 편하다)
 *
 * 캡처 화면: 드래그 = 영역 선택, Esc / 오른쪽 클릭 = 취소
 * 핀:       드래그 = 이동, 휠 = 확대/축소, Ctrl+휠 = 투명도
 *           Ctrl+C = 복사(xclip 필요), Ctrl+S = 저장, 1 = 원래 크기,
 *           N = 새 캡처, 더블클릭 / Esc = 닫기, 오른쪽 클릭 = 메뉴
 */
#define _DEFAULT_SOURCE
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xatom.h>
#include <X11/keysym.h>
#include <X11/cursorfont.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#define BORDER_RGB 0x3daee9
#define FLASH_MS   400
#define DCLICK_MS  350
#define MAX_PINS   256
#define MAX_PIXELS 40000000.0 /* 확대했을 때 이보다 크면 더 키우지 않는다 */

static Display *dpy;
static Window root;
static Visual *vis;
static int depth, SW, SH;
static GC gc;
static XFontStruct *font;
static Atom a_opacity;
static Cursor cur_cross, cur_move;
static unsigned long border_px;
static long capture_at; /* 새 캡처 예약 시각(ms), 0 = 없음 */

static long now_ms(void)
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec * 1000L + tv.tv_usec / 1000;
}

static int iround(double v) { return v < 0 ? (int)(v - 0.5) : (int)(v + 0.5); }

/* ---------- 픽셀 값 <-> RGB ---------- */

typedef struct { unsigned long mask, max; int shift; } Chan;
static Chan ch[3];

static void chan_init(Chan *c, unsigned long m)
{
    c->mask = m;
    c->shift = 0;
    while (m && !(m & 1)) { m >>= 1; c->shift++; }
    c->max = m;
}

static unsigned long rgb_pixel(unsigned rgb)
{
    unsigned v[3] = { (rgb >> 16) & 255, (rgb >> 8) & 255, rgb & 255 };
    unsigned long p = 0;
    for (int i = 0; i < 3; i++)
        p |= (v[i] * ch[i].max / 255) << ch[i].shift;
    return p;
}

static void pixel_rgb(unsigned long p, unsigned char *out)
{
    for (int i = 0; i < 3; i++)
        out[i] = ch[i].max ? ((p & ch[i].mask) >> ch[i].shift) * 255 / ch[i].max : 0;
}

static unsigned long pixel_half(unsigned long p) /* 색을 절반 밝기로 */
{
    unsigned long q = 0;
    for (int i = 0; i < 3; i++)
        q |= ((p & ch[i].mask) >> 1) & ch[i].mask;
    return q;
}

/* ---------- 글자 ---------- */

static int text_w(const char *s) { return font ? XTextWidth(font, s, strlen(s)) : 6 * (int)strlen(s); }
static int font_asc(void) { return font ? font->ascent : 10; }
static int font_h(void) { return font ? font->ascent + font->descent : 13; }

static void draw_text(Drawable d, int x, int y, const char *s, unsigned fg)
{
    XSetForeground(dpy, gc, rgb_pixel(fg));
    XDrawString(dpy, d, gc, x, y, s, strlen(s));
}

/* ---------- PNG (압축 없는 deflate) ---------- */

typedef struct { int w, h; unsigned char *rgb; } Img;

static unsigned long crc_tab[256];

static unsigned long crc32_upd(unsigned long c, const unsigned char *b, size_t n)
{
    if (!crc_tab[1])
        for (unsigned long i = 0; i < 256; i++) {
            unsigned long k = i;
            for (int j = 0; j < 8; j++)
                k = (k & 1) ? 0xedb88320UL ^ (k >> 1) : k >> 1;
            crc_tab[i] = k;
        }
    c ^= 0xffffffffUL;
    while (n--)
        c = crc_tab[(c ^ *b++) & 0xff] ^ (c >> 8);
    return c ^ 0xffffffffUL;
}

static void put32(unsigned char *p, unsigned long v)
{
    p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v;
}

static void png_chunk(FILE *f, const char *type, const unsigned char *data, size_t len)
{
    unsigned char b[4];
    put32(b, len);
    fwrite(b, 1, 4, f);
    fwrite(type, 1, 4, f);
    if (len)
        fwrite(data, 1, len, f);
    put32(b, crc32_upd(crc32_upd(0, (const unsigned char *)type, 4), data, len));
    fwrite(b, 1, 4, f);
}

static int png_write(FILE *f, const Img *im)
{
    size_t row = (size_t)im->w * 3 + 1, raw = row * im->h;
    unsigned char *r = malloc(raw), *z = malloc(raw + (raw / 65535 + 1) * 5 + 6), *p = z;
    if (!r || !z) {
        free(r); free(z);
        return -1;
    }
    for (int y = 0; y < im->h; y++) {
        r[y * row] = 0; /* 필터 없음 */
        memcpy(r + y * row + 1, im->rgb + (size_t)y * im->w * 3, (size_t)im->w * 3);
    }
    *p++ = 0x78; *p++ = 0x01;
    for (size_t off = 0; off < raw;) {
        size_t n = raw - off > 65535 ? 65535 : raw - off;
        *p++ = off + n == raw;
        *p++ = n & 255; *p++ = n >> 8;
        *p++ = ~n & 255; *p++ = (~n >> 8) & 255;
        memcpy(p, r + off, n);
        p += n; off += n;
    }
    unsigned long s1 = 1, s2 = 0;
    for (size_t i = 0; i < raw;) {
        size_t end = i + 5552 < raw ? i + 5552 : raw;
        for (; i < end; i++) { s1 += r[i]; s2 += s1; }
        s1 %= 65521; s2 %= 65521;
    }
    put32(p, (s2 << 16) | s1);
    p += 4;

    unsigned char hdr[13];
    put32(hdr, im->w);
    put32(hdr + 4, im->h);
    hdr[8] = 8; hdr[9] = 2; hdr[10] = hdr[11] = hdr[12] = 0; /* 8비트 RGB */
    fwrite("\x89PNG\r\n\x1a\n", 1, 8, f);
    png_chunk(f, "IHDR", hdr, 13);
    png_chunk(f, "IDAT", z, p - z);
    png_chunk(f, "IEND", NULL, 0);
    free(r); free(z);
    return ferror(f) ? -1 : 0;
}

/* ---------- 핀 ---------- */

typedef struct {
    Window win;
    Pixmap pm;
    Img img;
    int x, y, w, h, dx, dy;
    double scale, alpha;
    unsigned long border;
    long flash_end;
    Time last_click;
} Pin;

static Pin *pins[MAX_PINS];
static int npins;

static void menu_close(void);
static struct { Window win; Pin *pin; int sel, w, ih; Time opened; } menu;

static Pin *pin_find(Window w)
{
    for (int i = 0; i < npins; i++)
        if (pins[i]->win == w)
            return pins[i];
    return NULL;
}

static void pin_draw(Pin *p)
{
    XCopyArea(dpy, p->pm, p->win, gc, 0, 0, p->w, p->h, 0, 0);
    XSetForeground(dpy, gc, p->border);
    XDrawRectangle(dpy, p->win, gc, 0, 0, p->w - 1, p->h - 1);
}

/* 지금 배율로 그림을 다시 만든다(쌍선형 보간) */
static void pin_render(Pin *p)
{
    const Img *s = &p->img;
    int w = iround(s->w * p->scale), h = iround(s->h * p->scale);
    if (w < 1) w = 1;
    if (h < 1) h = 1;
    XImage *xi = XCreateImage(dpy, vis, depth, ZPixmap, 0, NULL, w, h, 32, 0);
    xi->data = malloc((size_t)xi->bytes_per_line * h);
    for (int y = 0; y < h; y++) {
        long fy = (long)(2 * y + 1) * s->h * 128 / h - 128;
        if (fy < 0) fy = 0;
        int y0 = fy >> 8, ty = fy & 255, y1 = y0 + 1 < s->h ? y0 + 1 : y0;
        for (int x = 0; x < w; x++) {
            long fx = (long)(2 * x + 1) * s->w * 128 / w - 128;
            if (fx < 0) fx = 0;
            int x0 = fx >> 8, tx = fx & 255, x1 = x0 + 1 < s->w ? x0 + 1 : x0;
            const unsigned char *a = s->rgb + ((size_t)y0 * s->w + x0) * 3,
                                *b = s->rgb + ((size_t)y0 * s->w + x1) * 3,
                                *c = s->rgb + ((size_t)y1 * s->w + x0) * 3,
                                *d = s->rgb + ((size_t)y1 * s->w + x1) * 3;
            unsigned v = 0;
            for (int i = 0; i < 3; i++) {
                unsigned top = a[i] * (256 - tx) + b[i] * tx, bot = c[i] * (256 - tx) + d[i] * tx;
                v = v << 8 | ((top * (256 - ty) + bot * ty) >> 16);
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
    a.override_redirect = True;
    a.background_pixmap = None;
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

static void pin_zoom(Pin *p, int rx, int ry, double f)
{
    double s = p->scale * f;
    if (s < 0.1) s = 0.1;
    if (s > 8.0) s = 8.0;
    if (s > 0.999 && s < 1.001) s = 1.0;
    if (s == p->scale || (double)p->img.w * s * p->img.h * s > MAX_PIXELS)
        return;
    /* 마우스가 가리키는 점이 제자리에 있도록 위치도 옮긴다 */
    double k = s / p->scale;
    p->x = iround(rx - (rx - p->x) * k);
    p->y = iround(ry - (ry - p->y) * k);
    p->scale = s;
    pin_render(p);
}

static void pin_reset(Pin *p)
{
    p->scale = 1.0;
    pin_render(p);
}

static void pin_fade(Pin *p, double step)
{
    /* 투명도는 컴포지터(창 효과)가 켜진 환경에서만 보인다 */
    p->alpha += step;
    if (p->alpha < 0.2) p->alpha = 0.2;
    if (p->alpha > 0.999) p->alpha = 1.0;
    if (p->alpha == 1.0) {
        XDeleteProperty(dpy, p->win, a_opacity);
    } else {
        unsigned long v = (unsigned long)(p->alpha * 0xffffffffUL);
        XChangeProperty(dpy, p->win, a_opacity, XA_CARDINAL, 32, PropModeReplace, (unsigned char *)&v, 1);
    }
}

static void pin_flash(Pin *p, unsigned rgb)
{
    p->border = rgb_pixel(rgb);
    p->flash_end = now_ms() + FLASH_MS;
    pin_draw(p);
}

static void pin_copy(Pin *p)
{
    FILE *f = popen("xclip -selection clipboard -t image/png -i 2>/dev/null", "w");
    int ok = 0;
    if (f) {
        png_write(f, &p->img);
        ok = pclose(f) == 0;
    }
    if (!ok)
        fprintf(stderr, "복사하려면 xclip 이 필요합니다: sudo apt install xclip\n");
    pin_flash(p, ok ? 0x00ff00 : 0xff0000);
}

static void pin_save(Pin *p)
{
    const char *home = getenv("HOME");
    char dir[4096], path[4200], stamp[32];
    struct stat st;
    if (!home)
        home = ".";
    snprintf(dir, sizeof dir, "%s/Pictures", home);
    if (stat(dir, &st) || !S_ISDIR(st.st_mode))
        snprintf(dir, sizeof dir, "%s", home);
    time_t t = time(NULL);
    strftime(stamp, sizeof stamp, "%Y%m%d-%H%M%S", localtime(&t));
    snprintf(path, sizeof path, "%s/snappin-%s.png", dir, stamp);

    FILE *f = fopen(path, "wb");
    int ok = f && png_write(f, &p->img) == 0;
    if (f && fclose(f))
        ok = 0;
    if (ok)
        printf("저장: %s\n", path);
    else
        fprintf(stderr, "저장하지 못했습니다: %s\n", path);
    fflush(stdout);
    pin_flash(p, ok ? 0x00ff00 : 0xff0000);
}

static void new_capture(void) { capture_at = now_ms() + 200; } /* 메뉴가 사라진 뒤에 찍는다 */

static void close_all(void)
{
    while (npins)
        pin_close(pins[0]);
}

/* ---------- 오른쪽 클릭 메뉴 ---------- */

static const char *menu_label[] = { "Copy", "Save", "Actual size", "New capture", "Close", "Close all" };
static const char *menu_key[] = { "Ctrl+C", "Ctrl+S", "1", "N", "Esc", "" };
#define MENU_N 6

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

static int menu_hit(int x, int y)
{
    return x >= 0 && x < menu.w && y >= 0 && y < menu.ih * MENU_N ? y / menu.ih : -1;
}

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
            menu_close();
        break;
    case ButtonRelease: {
        int s = menu_hit(e->xbutton.x, e->xbutton.y);
        if (s < 0 || e->xbutton.time - menu.opened < 250) /* 메뉴를 연 오른쪽 클릭을 뗀 것은 무시 */
            break;
        Pin *p = menu.pin;
        menu_close();
        switch (s) {
        case 0: pin_copy(p); break;
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

static void pin_event(Pin *p, XEvent *e)
{
    switch (e->type) {
    case Expose:
        if (e->xexpose.count == 0)
            pin_draw(p);
        break;
    case EnterNotify:
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
            p->dx = b->x_root - p->x;
            p->dy = b->y_root - p->y;
            XRaiseWindow(dpy, p->win);
        } else if (b->button == Button3) {
            menu_open(p, b->x_root, b->y_root, b->time);
        } else if (b->button == Button4) {
            if (ctrl) pin_fade(p, 0.1);
            else pin_zoom(p, b->x_root, b->y_root, 1.1);
        } else if (b->button == Button5) {
            if (ctrl) pin_fade(p, -0.1);
            else pin_zoom(p, b->x_root, b->y_root, 1 / 1.1);
        }
        break;
    }
    case MotionNotify:
        while (XCheckTypedWindowEvent(dpy, p->win, MotionNotify, e))
            ; /* 가장 최근 위치만 쓴다 */
        p->x = e->xmotion.x_root - p->dx;
        p->y = e->xmotion.y_root - p->dy;
        XMoveWindow(dpy, p->win, p->x, p->y);
        break;
    case KeyPress: {
        KeySym k = XLookupKeysym(&e->xkey, 0);
        int ctrl = e->xkey.state & ControlMask;
        if (k == XK_Escape) pin_close(p);
        else if (ctrl && k == XK_c) pin_copy(p);
        else if (ctrl && k == XK_s) pin_save(p);
        else if (!ctrl && k == XK_1) pin_reset(p);
        else if (!ctrl && k == XK_n) new_capture();
        break;
    }
    }
}

/* ---------- 영역 고르기 ---------- */

static struct {
    int active, pressing, box, sx, sy, x0, y0, x1, y1;
    Window win;
    Pixmap orig, dark, back;
    XImage *shot;
} sel;

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
        int ly = sel.y0 > font_h() + 8 ? sel.y0 - 6 : sel.y1 + font_asc() + 6;
        draw_text(sel.back, sel.x0 + 1, ly + 1, t, 0x000000);
        draw_text(sel.back, sel.x0, ly, t, 0xffffff);
    }
    XCopyArea(dpy, sel.back, sel.win, gc, 0, 0, SW, SH, 0, 0);
}

static void start_capture(void)
{
    if (sel.active)
        return;
    XImage *shot = XGetImage(dpy, root, 0, 0, SW, SH, AllPlanes, ZPixmap);
    if (!shot) {
        fprintf(stderr, "화면을 찍지 못했습니다. X11 세션인지 확인하세요.\n");
        return;
    }
    /* 어둡게 한 사본 */
    size_t n = (size_t)shot->bytes_per_line * SH;
    char *d = malloc(n);
    memcpy(d, shot->data, n);
    XImage *dark = XCreateImage(dpy, vis, shot->depth, ZPixmap, 0, d, SW, SH, shot->bitmap_pad, shot->bytes_per_line);
    uint16_t one = 1;
    int host_lsb = *(unsigned char *)&one == 1;
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

    sel.orig = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.dark = XCreatePixmap(dpy, root, SW, SH, depth);
    sel.back = XCreatePixmap(dpy, root, SW, SH, depth);
    XPutImage(dpy, sel.orig, gc, shot, 0, 0, 0, 0, SW, SH);
    XPutImage(dpy, sel.dark, gc, dark, 0, 0, 0, 0, SW, SH);
    XDestroyImage(dark);
    sel.shot = shot;

    XSetWindowAttributes a = { 0 };
    a.override_redirect = True;
    a.background_pixmap = sel.dark;
    a.cursor = cur_cross;
    a.event_mask = ExposureMask | ButtonPressMask | ButtonReleaseMask | PointerMotionMask | KeyPressMask;
    sel.win = XCreateWindow(dpy, root, 0, 0, SW, SH, 0, CopyFromParent, InputOutput, CopyFromParent,
                            CWOverrideRedirect | CWBackPixmap | CWCursor | CWEventMask, &a);
    XMapRaised(dpy, sel.win);
    XSync(dpy, False);
    sel.active = 1;
    sel.pressing = sel.box = 0;

    /* 키보드·마우스를 이 창으로 가져온다 */
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

static void sel_finish(int take)
{
    XUngrabPointer(dpy, CurrentTime);
    XUngrabKeyboard(dpy, CurrentTime);
    XDestroyWindow(dpy, sel.win);
    if (take) {
        int w = sel.x1 - sel.x0, h = sel.y1 - sel.y0;
        Img im = { w, h, malloc((size_t)w * h * 3) };
        for (int y = 0; y < h; y++)
            for (int x = 0; x < w; x++)
                pixel_rgb(XGetPixel(sel.shot, sel.x0 + x, sel.y0 + y), im.rgb + ((size_t)y * w + x) * 3);
        pin_new(im, sel.x0, sel.y0);
    }
    XFreePixmap(dpy, sel.orig);
    XFreePixmap(dpy, sel.dark);
    XFreePixmap(dpy, sel.back);
    XDestroyImage(sel.shot);
    sel.active = 0;
}

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
            ;
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
        } else { /* 너무 작으면 다시 고르게 둔다 */
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

/* ---------- 시작 ---------- */

static int on_xerror(Display *d, XErrorEvent *e)
{
    (void)d; (void)e; /* 이미 닫힌 창에 대한 요청 같은 것은 무시한다 */
    return 0;
}

int main(void)
{
    signal(SIGPIPE, SIG_IGN);
    dpy = XOpenDisplay(NULL);
    if (!dpy) {
        fprintf(stderr, "X11 화면(DISPLAY)을 찾지 못했습니다. X11 세션에서 실행하세요.\n");
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
        fprintf(stderr, "트루컬러(24비트) 화면에서만 동작합니다.\n");
        return 1;
    }
    chan_init(&ch[0], vis->red_mask);
    chan_init(&ch[1], vis->green_mask);
    chan_init(&ch[2], vis->blue_mask);
    border_px = rgb_pixel(BORDER_RGB);

    gc = XCreateGC(dpy, root, 0, NULL);
    font = XLoadQueryFont(dpy, "-misc-fixed-bold-r-normal--13-*-*-*-*-*-iso8859-1");
    if (!font)
        font = XLoadQueryFont(dpy, "fixed");
    if (font)
        XSetFont(dpy, gc, font->fid);
    a_opacity = XInternAtom(dpy, "_NET_WM_WINDOW_OPACITY", False);
    cur_cross = XCreateFontCursor(dpy, XC_crosshair);
    cur_move = XCreateFontCursor(dpy, XC_fleur);

    start_capture();

    int fd = ConnectionNumber(dpy);
    for (;;) {
        while (XPending(dpy)) {
            XEvent e;
            Pin *p;
            XNextEvent(dpy, &e);
            if (sel.active && e.xany.window == sel.win)
                sel_event(&e);
            else if (menu.win && e.xany.window == menu.win)
                menu_event(&e);
            else if ((p = pin_find(e.xany.window)))
                pin_event(p, &e);
        }

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
        if (!npins && !sel.active && !capture_at)
            break; /* 떠 있는 그림을 모두 닫으면 끝 */
        if (XPending(dpy))
            continue;

        fd_set fds;
        FD_ZERO(&fds);
        FD_SET(fd, &fds);
        struct timeval tv = { wait / 1000, (wait % 1000) * 1000 };
        select(fd + 1, &fds, NULL, NULL, wait >= 0 ? &tv : NULL);
    }
    XCloseDisplay(dpy);
    return 0;
}
