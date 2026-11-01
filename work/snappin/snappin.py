#!/usr/bin/env python3
# snappin.py — X11에서 드래그로 화면 일부를 찍고, 찍은 그림을 같은 자리에 떠 있게(핀) 띄운다.
# 필요: python3, tkinter, Pillow
#   Debian/Ubuntu: sudo apt install python3-tk python3-pil python3-pil.imagetk
# 실행: python3 snappin.py   (단축키에 연결해 두면 편하다)
#
# 캡처 화면: 드래그 = 영역 선택, Esc / 오른쪽 클릭 = 취소
# 핀:       드래그 = 이동, 휠 = 확대/축소, Ctrl+휠 = 투명도
#           Ctrl+C = 복사(xclip 필요), Ctrl+S = 저장, 1 = 원래 크기,
#           N = 새 캡처, 더블클릭 / Esc = 닫기, 오른쪽 클릭 = 메뉴

import io
import os
import shutil
import subprocess
import sys
import tempfile
import time
import tkinter as tk

try:
    from PIL import Image, ImageTk
except ImportError:
    sys.exit("Pillow가 필요합니다: pip install pillow "
             "(또는 sudo apt install python3-pil python3-pil.imagetk)")

BORDER = "#3daee9"


def grab_screen():
    """화면 전체(모든 모니터)를 그림으로 가져온다."""
    try:
        from PIL import ImageGrab
        img = ImageGrab.grab()  # 리눅스에서는 X11 루트 창 전체
        if img is not None:
            return img.convert("RGB")
    except Exception:
        pass
    # Pillow가 XCB 없이 빌드된 경우 외부 도구로 대신 찍는다
    fd, tmp = tempfile.mkstemp(suffix=".png")
    os.close(fd)
    try:
        for cmd in (["maim", tmp], ["import", "-window", "root", tmp], ["scrot", "-o", tmp]):
            if not shutil.which(cmd[0]):
                continue
            try:
                subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                with Image.open(tmp) as im:
                    return im.convert("RGB")
            except Exception:
                continue
    finally:
        os.remove(tmp)
    return None


class App:
    def __init__(self):
        self.root = tk.Tk()
        self.root.withdraw()
        self.pins = []
        self.selecting = False

    def capture(self):
        if self.selecting:
            return
        shot = grab_screen()
        if shot is None:
            print("화면을 찍지 못했습니다. X11 세션인지 확인하고, "
                  "maim 이나 scrot 을 설치해 보세요.", file=sys.stderr)
            self.maybe_quit()
            return
        self.selecting = True
        Selector(self, shot)

    def selector_done(self, shot, box):
        self.selecting = False
        if box:
            self.pins.append(Pin(self, shot.crop(box), box[0], box[1]))
        self.maybe_quit()

    def pin_closed(self, pin):
        if pin in self.pins:
            self.pins.remove(pin)
        self.maybe_quit()

    def close_all(self):
        for pin in list(self.pins):
            pin.close()

    def maybe_quit(self):
        if not self.pins and not self.selecting:
            self.root.destroy()

    def run(self):
        self.root.after(0, self.capture)
        self.root.mainloop()


class Selector:
    """찍어 둔 화면을 전체 화면으로 덮고 드래그로 영역을 고른다."""

    def __init__(self, app, shot):
        self.app, self.shot = app, shot
        self.w, self.h = shot.size
        self.start = None
        self.box = None

        win = self.win = tk.Toplevel(app.root)
        win.overrideredirect(True)
        win.geometry(f"{self.w}x{self.h}+0+0")
        win.attributes("-topmost", True)

        self.photo = ImageTk.PhotoImage(shot)
        c = self.c = tk.Canvas(win, width=self.w, height=self.h,
                               highlightthickness=0, bd=0, cursor="crosshair")
        c.pack()
        c.create_image(0, 0, anchor="nw", image=self.photo)
        # 고른 영역 바깥을 어둡게 덮는 사각형 네 개
        self.shades = [c.create_rectangle(0, 0, 0, 0, fill="black", stipple="gray50", width=0)
                       for _ in range(4)]
        self.frame = c.create_rectangle(0, 0, 0, 0, outline=BORDER, width=1, state="hidden")
        self.label = c.create_text(0, 0, anchor="sw", fill="white",
                                   font=("TkDefaultFont", 11, "bold"), state="hidden")
        self.draw()

        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_motion)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Button-3>", lambda e: self.finish(None))
        win.bind("<Escape>", lambda e: self.finish(None))
        self.tries = 0
        win.after(30, self.take_input)

    def take_input(self):
        # 창이 뜬 뒤 키보드·마우스를 이 창으로 가져온다
        try:
            self.win.focus_force()
            self.win.grab_set_global()
        except tk.TclError:
            self.tries += 1
            if self.tries < 20:
                self.win.after(50, self.take_input)

    def draw(self):
        c, w, h = self.c, self.w, self.h
        if not self.box:
            c.coords(self.shades[0], 0, 0, w, h)
            for s in self.shades[1:]:
                c.coords(s, 0, 0, 0, 0)
            c.itemconfigure(self.frame, state="hidden")
            c.itemconfigure(self.label, state="hidden")
            return
        x0, y0, x1, y1 = self.box
        c.coords(self.shades[0], 0, 0, w, y0)
        c.coords(self.shades[1], 0, y1, w, h)
        c.coords(self.shades[2], 0, y0, x0, y1)
        c.coords(self.shades[3], x1, y0, w, y1)
        c.coords(self.frame, x0 - 1, y0 - 1, x1, y1)
        c.itemconfigure(self.frame, state="normal")
        ly = y0 - 4 if y0 > 20 else y1 + 18
        c.coords(self.label, x0, ly)
        c.itemconfigure(self.label, text=f"{x1 - x0} × {y1 - y0}", state="normal")

    def clamp(self, x, y):
        return min(max(x, 0), self.w), min(max(y, 0), self.h)

    def on_press(self, e):
        self.start = self.clamp(e.x, e.y)
        self.box = None
        self.draw()

    def on_motion(self, e):
        if not self.start:
            return
        (sx, sy), (x, y) = self.start, self.clamp(e.x, e.y)
        self.box = (min(sx, x), min(sy, y), max(sx, x), max(sy, y))
        self.draw()

    def on_release(self, e):
        self.on_motion(e)
        box, self.start = self.box, None
        if box and box[2] - box[0] >= 3 and box[3] - box[1] >= 3:
            self.finish(box)
        else:  # 너무 작으면 다시 고르게 둔다
            self.box = None
            self.draw()

    def finish(self, box):
        try:
            self.win.grab_release()
        except tk.TclError:
            pass
        self.win.destroy()
        self.app.selector_done(self.shot, box)


class Pin:
    """찍은 그림을 찍은 자리에 테두리 없는 창으로 띄운다."""

    def __init__(self, app, img, x, y):
        self.app, self.orig = app, img
        self.x, self.y = x, y
        self.scale, self.alpha = 1.0, 1.0
        self.closed = False

        win = self.win = tk.Toplevel(app.root)
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        c = self.c = tk.Canvas(win, highlightthickness=0, bd=0, cursor="fleur")
        c.pack()
        self.render()

        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<Double-Button-1>", lambda e: self.close())
        c.bind("<Button-3>", self.popup)
        c.bind("<Button-4>", lambda e: self.zoom(e, 1.1))   # X11 휠 위
        c.bind("<Button-5>", lambda e: self.zoom(e, 1 / 1.1))  # X11 휠 아래
        c.bind("<MouseWheel>", lambda e: self.zoom(e, 1.1 if e.delta > 0 else 1 / 1.1))
        c.bind("<Control-Button-4>", lambda e: self.fade(0.1))
        c.bind("<Control-Button-5>", lambda e: self.fade(-0.1))
        c.bind("<Enter>", lambda e: win.focus_force())
        win.bind("<Escape>", lambda e: self.close())
        win.bind("<Control-c>", lambda e: self.copy())
        win.bind("<Control-s>", lambda e: self.save())
        win.bind("<Key-1>", lambda e: self.reset())
        win.bind("<Key-n>", lambda e: self.new_capture())

        m = self.menu = tk.Menu(win, tearoff=0)
        m.add_command(label="복사  (Ctrl+C)", command=self.copy)
        m.add_command(label="저장  (Ctrl+S)", command=self.save)
        m.add_command(label="원래 크기  (1)", command=self.reset)
        m.add_command(label="새 캡처  (N)", command=self.new_capture)
        m.add_separator()
        m.add_command(label="닫기  (Esc)", command=self.close)
        m.add_command(label="모두 닫기", command=app.close_all)

    def size(self):
        return (max(1, round(self.orig.width * self.scale)),
                max(1, round(self.orig.height * self.scale)))

    def render(self, outline=BORDER):
        w, h = self.size()
        img = self.orig if self.scale == 1 else self.orig.resize((w, h), Image.LANCZOS)
        self.photo = ImageTk.PhotoImage(img)
        c = self.c
        c.config(width=w, height=h)
        c.delete("all")
        c.create_image(0, 0, anchor="nw", image=self.photo)
        self.border = c.create_rectangle(0, 0, w - 1, h - 1, outline=outline)
        self.win.geometry(f"{w}x{h}+{self.x}+{self.y}")

    def on_press(self, e):
        self.dx, self.dy = e.x_root - self.x, e.y_root - self.y

    def on_drag(self, e):
        self.x, self.y = e.x_root - self.dx, e.y_root - self.dy
        self.win.geometry(f"+{self.x}+{self.y}")

    def zoom(self, e, factor):
        new = min(max(self.scale * factor, 0.1), 8.0)
        if new == self.scale:
            return
        # 마우스가 가리키는 점이 제자리에 있도록 위치도 옮긴다
        k = new / self.scale
        self.x = round(e.x_root - (e.x_root - self.x) * k)
        self.y = round(e.y_root - (e.y_root - self.y) * k)
        self.scale = new
        self.render()

    def reset(self):
        self.scale = 1.0
        self.render()

    def fade(self, step):
        # 투명도는 컴포지터(창 효과)가 켜진 환경에서만 보인다
        self.alpha = min(max(self.alpha + step, 0.2), 1.0)
        self.win.attributes("-alpha", self.alpha)

    def flash(self, color):
        self.c.itemconfigure(self.border, outline=color)
        self.win.after(400, lambda: self.closed or self.c.itemconfigure(self.border, outline=BORDER))

    def copy(self):
        if not shutil.which("xclip"):
            print("복사하려면 xclip 이 필요합니다: sudo apt install xclip", file=sys.stderr)
            self.flash("red")
            return
        buf = io.BytesIO()
        self.orig.save(buf, "PNG")
        p = subprocess.Popen(["xclip", "-selection", "clipboard", "-t", "image/png", "-i"],
                             stdin=subprocess.PIPE)
        p.communicate(buf.getvalue())
        self.flash("lime")

    def save(self):
        folder = os.path.expanduser("~/Pictures")
        if not os.path.isdir(folder):
            folder = os.path.expanduser("~")
        path = os.path.join(folder, time.strftime("snappin-%Y%m%d-%H%M%S.png"))
        self.orig.save(path)
        print("저장:", path)
        self.flash("lime")

    def new_capture(self):
        self.app.root.after(200, self.app.capture)  # 메뉴가 사라진 뒤에 찍는다

    def popup(self, e):
        try:
            self.menu.tk_popup(e.x_root, e.y_root)
        finally:
            self.menu.grab_release()

    def close(self):
        if self.closed:
            return
        self.closed = True
        self.win.destroy()
        self.app.pin_closed(self)


if __name__ == "__main__":
    if sys.platform.startswith("linux") and not os.environ.get("DISPLAY"):
        sys.exit("X11 화면(DISPLAY)을 찾지 못했습니다. X11 세션에서 실행하세요.")
    App().run()
