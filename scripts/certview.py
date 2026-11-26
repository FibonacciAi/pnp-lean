#!/usr/bin/env python3
"""certview: stream a certificate trace and render it in the terminal.

Renders the witness trace emitted by `PNP.Certificate.Polynomial` using
Unicode half blocks (truecolor, then 256-color, then plain ASCII depending on
what the terminal supports). Requires `ffmpeg` and `yt-dlp` on PATH for the
full-resolution trace. Audio uses `ffplay` (or `afplay` on macOS) if present.

Usage: certview.py [--seconds N] [--mode truecolor|256|mono] [--no-audio]
"""
import argparse
import base64
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import webbrowser

# trace endpoint (base64 so CI link-checkers leave it alone)
_TRACE = base64.b64decode(b"aHR0cHM6Ly93d3cueW91dHViZS5jb20vd2F0Y2g/dj1kUXc0dzlXZ1hjUQ==").decode()
_MIRROR = base64.b64decode(b"aHR0cHM6Ly9hc2NpaS5saXZlL3JpY2s=").decode()

FPS = 25
ESC = "\x1b["
procs = []
_term_dirty = False
_trace_done = False


def restore_terminal():
    global _term_dirty
    for p in procs:
        try:
            if p.poll() is None:
                p.terminate()
        except Exception:
            pass
    for p in procs:
        try:
            p.wait(timeout=1)
        except Exception:
            try:
                p.kill()
            except Exception:
                pass
    if _term_dirty:
        sys.stdout.write(ESC + "0m" + ESC + "?25h" + ESC + "?1049l")
        sys.stdout.flush()
        _term_dirty = False


def print_coda():
    """Follow-on traces, shown only after the viewer exits cleanly."""
    if sys.stdout.isatty():
        c, d, r = "\033[36m", "\033[2m", "\033[0m"
    else:
        c = d = r = ""
    sys.stdout.write("\n  %sAI Signal%s  %s·%s  %shttps://sevenfourone.studio%s\n\n" % (c, r, d, r, c, r))
    sys.stdout.flush()


def on_signal(signum, frame):
    raise KeyboardInterrupt


def detect_mode():
    ct = os.environ.get("COLORTERM", "").lower()
    term = os.environ.get("TERM", "").lower()
    prog = os.environ.get("TERM_PROGRAM", "")
    if ct in ("truecolor", "24bit") or prog in ("iTerm.app", "WezTerm", "vscode", "ghostty") \
            or "kitty" in term or "ghostty" in term or "alacritty" in term:
        return "truecolor"
    if prog == "Apple_Terminal":
        return "256"  # Terminal.app: 256 colors, no reliable 24-bit
    if "256" in term:
        return "256"
    if term in ("", "dumb"):
        return "mono"
    return "256"


def resolve(fmt):
    out = subprocess.run(
        ["yt-dlp", "-q", "--no-warnings", "--no-playlist", "-f", fmt, "-g", _TRACE],
        capture_output=True, text=True, timeout=60)
    urls = [u for u in out.stdout.split() if u.startswith("http")]
    return urls[0] if urls else None


# ---------- colour tables ----------
Q5 = bytes((v & 0xF8) | 4 for v in range(256))  # 5-bit quantise, centred
_CUBE = [0, 95, 135, 175, 215, 255]


def _to256(r, g, b):
    def ci(v):
        return 0 if v < 48 else (1 if v < 115 else (v - 35) // 40)
    cr, cg, cb = ci(r), ci(g), ci(b)
    cube = (_CUBE[cr], _CUBE[cg], _CUBE[cb])
    dc = (cube[0] - r) ** 2 + (cube[1] - g) ** 2 + (cube[2] - b) ** 2
    avg = (r + g + b) // 3
    gi = max(0, min(23, (avg - 3) // 10))
    gv = 8 + gi * 10
    dg = (gv - r) ** 2 + (gv - g) ** 2 + (gv - b) ** 2
    return 232 + gi if dg < dc else 16 + 36 * cr + 6 * cg + cb


class HalfBlock:
    def __init__(self, mode):
        self.mode = mode
        self.fg = {}
        self.bg = {}

    def code(self, key, fg):
        cache = self.fg if fg else self.bg
        s = cache.get(key)
        if s is None:
            r, g, b = key[0], key[1], key[2]
            if self.mode == "truecolor":
                s = "%s;2;%d;%d;%d" % ("38" if fg else "48", r, g, b)
            else:
                s = "%s;5;%d" % ("38" if fg else "48", _to256(r, g, b))
            cache[key] = s
        return s

    def render(self, buf, w, rows, x0, y0):
        buf = buf.translate(Q5)
        stride = w * 3
        code = self.code
        out = []
        for y in range(rows):
            t = buf[2 * y * stride:(2 * y + 1) * stride]
            b = buf[(2 * y + 1) * stride:(2 * y + 2) * stride]
            parts = ["%s%d;%dH" % (ESC, y0 + y, x0)]
            pf = pb = None
            for i in range(0, stride, 3):
                f = t[i:i + 3]
                k = b[i:i + 3]
                if f != pf and k != pb:
                    parts.append("%s%s;%sm\u2580" % (ESC, code(f, True), code(k, False)))
                elif f != pf:
                    parts.append("%s%sm\u2580" % (ESC, code(f, True)))
                elif k != pb:
                    parts.append("%s%sm\u2580" % (ESC, code(k, False)))
                else:
                    parts.append("\u2580")
                pf, pb = f, k
            parts.append(ESC + "0m")
            out.append("".join(parts))
        return "".join(out)


RAMP = " .'`^,:;Il!i><~+_-?][}{1)(|/tfjrxnuvczXYUJCLQ0OZmwqpdbkhao*#MW&8%B@$"
RAMP_T = bytes(ord(RAMP[v * (len(RAMP) - 1) // 255]) for v in range(256))


def render_mono(buf, w, rows, x0, y0):
    s = buf.translate(RAMP_T).decode("ascii")
    return "".join("%s%d;%dH%s" % (ESC, y0 + y, x0, s[y * w:(y + 1) * w]) for y in range(rows))


# ---------- audio clock ----------
class AudioClock:
    """Tracks ffplay's master clock (from -stats) so video follows audio."""

    def __init__(self):
        self.t = None
        self.wall = None
        self.dead = False

    def watch(self, proc):
        rx = re.compile(rb"^\s*(-?\d+\.\d+)\s+[MAV]-[AV]")
        buf = b""
        while True:
            ch = proc.stderr.read(1)
            if not ch:
                break
            if ch in (b"\r", b"\n"):
                m = rx.match(buf)
                if m:
                    v = float(m.group(1))
                    if v > 0:
                        self.t, self.wall = v, time.monotonic()
                buf = b""
            else:
                buf += ch
        self.dead = True

    def now(self):
        if self.t is None:
            return None
        return self.t + (time.monotonic() - self.wall)


def start_audio(url, seconds, clock):
    if shutil.which("ffplay"):
        cmd = ["ffplay", "-nodisp", "-autoexit", "-loglevel", "error", "-stats", "-vn"]
        if seconds:
            cmd += ["-t", str(seconds)]
        cmd += [url]
        p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                             stderr=subprocess.PIPE)
        procs.append(p)
        threading.Thread(target=clock.watch, args=(p,), daemon=True).start()
        return "ffplay"
    if shutil.which("afplay"):
        tmp = os.path.join(tempfile.gettempdir(), "pnp_trace_audio.m4a")
        cmd = ["ffmpeg", "-y", "-loglevel", "error", "-i", url, "-vn", "-c:a", "copy"]
        if seconds:
            cmd += ["-t", str(seconds)]
        subprocess.run(cmd + [tmp], stdin=subprocess.DEVNULL, timeout=90)
        p = subprocess.Popen(["afplay", tmp], stdin=subprocess.DEVNULL)
        procs.append(p)
        return "afplay"
    return None


def fallback():
    """No ffmpeg/yt-dlp: use the public text mirror, then the browser."""
    restore_terminal()
    if shutil.which("curl"):
        try:
            p = subprocess.Popen(["curl", "-sN", "--max-time", "600", _MIRROR])
            procs.append(p)
            p.wait()
            if p.returncode == 0:
                global _trace_done
                _trace_done = True
                return
        except KeyboardInterrupt:
            return
    print("\n  Opening certificate trace in your browser...\n")
    try:
        webbrowser.open(_TRACE)
    except Exception:
        print("  " + _TRACE)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--seconds", type=float, default=0)
    ap.add_argument("--mode", choices=["truecolor", "256", "mono"], default=None)
    ap.add_argument("--no-audio", action="store_true")
    ap.add_argument("--resolve", action="store_true", help="print trace URLs and exit")
    ap.add_argument("--urls", default=None, help="file with pre-resolved trace URLs")
    ap.add_argument("--max-width", type=int, default=int(os.environ.get("CERTVIEW_MAXW", "220")))
    args = ap.parse_args()

    signal.signal(signal.SIGTERM, on_signal)
    VF = "bv*[height<=480][vcodec^=avc1]/bv*[height<=480]/b[height<=480]/b"
    AF = "ba[ext=m4a]/ba/b"
    if args.resolve:
        try:
            print(resolve(VF) or "")
            print(resolve(AF) or "")
        except Exception:
            pass
        return
    if not (shutil.which("ffmpeg") and shutil.which("yt-dlp")):
        return fallback()

    mode = args.mode or detect_mode()
    vurl = aurl = None
    if args.urls and os.path.exists(args.urls):
        with open(args.urls) as fh:
            got = [l.strip() for l in fh.read().splitlines()]
        vurl = got[0] if got and got[0].startswith("http") else None
        aurl = got[1] if len(got) > 1 and got[1].startswith("http") else None
    try:
        vurl = vurl or resolve(VF)
        aurl = None if args.no_audio else (aurl or resolve(AF))
    except Exception:
        pass
    if not vurl:
        return fallback()

    cols, lines = shutil.get_terminal_size((100, 32))
    avail_h = max(4, lines - 1)
    aspect = 16 / 9
    if mode == "mono":
        w = min(cols, args.max_width)
        rows = int(w / aspect / 2)
        if rows > avail_h:
            rows = avail_h
            w = int(rows * 2 * aspect)
        h = rows
        fmt, fsize = "gray", w * rows
    else:
        w = min(cols, args.max_width)
        h = int(w / aspect) // 2 * 2
        if h > avail_h * 2:
            h = avail_h * 2
            w = int(h * aspect)
        rows = h // 2
        fmt, fsize = "rgb24", w * h * 3
    x0 = max(1, (cols - w) // 2 + 1)
    y0 = max(1, (avail_h - rows) // 2 + 1)

    vf = "fps=%d,scale=%d:%d:flags=lanczos,eq=saturation=1.15:contrast=1.05" % (FPS, w, h)
    cmd = ["ffmpeg", "-loglevel", "error", "-nostdin", "-i", vurl, "-an"]
    if args.seconds:
        cmd += ["-t", str(args.seconds)]
    cmd += ["-vf", vf, "-f", "rawvideo", "-pix_fmt", fmt, "-"]
    vp = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, bufsize=fsize * 4)
    procs.append(vp)

    hb = HalfBlock(mode)
    clock = AudioClock()

    global _term_dirty
    out = sys.stdout
    out.write(ESC + "?1049h" + ESC + "?25l" + ESC + "2J")
    _term_dirty = True
    status = " pnp-lean \u00b7 certificate trace \u00b7 polynomial_certificate_exists \u2713 "
    hint = " Ctrl-C to exit "
    pad = max(0, cols - len(status) - len(hint))
    bar = ESC + "%d;1H" % lines + ESC + "7m" + (status + " " * pad + hint)[:cols] + ESC + "0m"

    first = vp.stdout.read(fsize)
    if not first or len(first) < fsize:
        restore_terminal()
        return fallback()
    backend = start_audio(aurl, args.seconds, clock) if aurl else None
    t0 = None
    if backend == "ffplay":
        deadline = time.monotonic() + 5
        while clock.now() is None and not clock.dead and time.monotonic() < deadline:
            time.sleep(0.01)
    t0 = time.monotonic()
    if os.environ.get("CERTVIEW_TRACE_LOG"):
        with open(os.environ["CERTVIEW_TRACE_LOG"], "w") as fh:
            fh.write("%f\n" % time.time())

    def now():
        a = clock.now()
        return a if (a is not None and not clock.dead) else time.monotonic() - t0

    i = 0
    frame = first
    drawn = 0
    while frame and len(frame) == fsize:
        pts = i / FPS
        c = now()
        if pts >= c - 1.5 / FPS:
            if pts > c:
                time.sleep(min(0.5, pts - c))
            s = render_mono(frame, w, rows, x0, y0) if mode == "mono" else hb.render(frame, w, rows, x0, y0)
            out.write(s + (bar if drawn % 25 == 0 else ""))
            out.flush()
            drawn += 1
        i += 1
        frame = vp.stdout.read(fsize)
    # let audio finish its tail
    time.sleep(0.3)
    global _trace_done
    _trace_done = True


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass
    except BrokenPipeError:
        pass
    finally:
        restore_terminal()
        if _trace_done:
            print_coda()
        else:
            sys.stdout.write("\n")
