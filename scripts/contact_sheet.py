#!/usr/bin/env python3
"""Draws a pack's contact sheet with the real player, camera and light, in headless Chrome, and writes one
image to contact-sheets/<pack>.png, which git ignores. It needs the Google Chrome app, or CHROME set to a
Chrome or Chromium binary. See docs/process/reskins.md."""
import glob, http.server, os, shutil, subprocess, sys, tempfile, threading

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
OUT = os.path.join(ROOT, "contact-sheets")
# With no device scaling, this window puts a sheet of radius 12 at about 90 pixels to a hex's side.
WIDTH, HEIGHT = 2200, 1480


def chrome():
    named = os.environ.get("CHROME")
    choices = [named] if named else []
    choices += ["/Applications/Google Chrome.app/Contents/MacOS/Google Chrome", shutil.which("google-chrome"), shutil.which("chromium")]
    choices += sorted(glob.glob(os.path.expanduser("~/Library/Caches/ms-playwright/chromium-*/chrome-mac/Chromium.app/Contents/MacOS/Chromium")))
    for c in choices:
        if c and os.path.exists(c):
            return c
    raise SystemExit("contact-sheet: no Chrome found. Set CHROME to a Chrome or Chromium binary.")


class Files(http.server.SimpleHTTPRequestHandler):
    scene = ""

    def translate_path(self, path):
        path = path.split("?")[0]
        if path == "/":
            return os.path.join(ROOT, "scripts", "contact_sheet.html")
        if path == "/sheet.gpc":
            return Files.scene
        if path.startswith("/vendor/"):
            return os.path.join(ROOT, "web", path[1:])
        if path.startswith("/assets/") and "/" not in path[8:]:
            found = glob.glob(os.path.join(ROOT, "packs", "*", "meshes", path[8:]))
            return found[0] if found else os.path.join(ROOT, "no-such-file")
        return os.path.join(ROOT, "no-such-file")

    def log_message(self, *args):
        pass


def main():
    if len(sys.argv) != 2:
        raise SystemExit("say which pack: make contact-sheet PACK=<id>")
    pack = sys.argv[1]
    os.makedirs(OUT, exist_ok=True)
    png = os.path.join(OUT, f"{pack}.png")
    with tempfile.TemporaryDirectory() as tmp:
        Files.scene = os.path.join(tmp, "sheet.gpc")
        subprocess.run([os.path.join(ROOT, ".lake/build/bin/charter-contact"), pack, Files.scene], check=True)
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Files)
        threading.Thread(target=server.serve_forever, daemon=True).start()
        url = f"http://127.0.0.1:{server.server_address[1]}/"
        base = [chrome(), "--headless=new", "--disable-gpu-vsync", "--use-angle=swiftshader", "--enable-unsafe-swiftshader",
                "--hide-scrollbars", f"--user-data-dir={tmp}/chrome", f"--window-size={WIDTH},{HEIGHT}", "--force-device-scale-factor=1",
                "--virtual-time-budget=20000", "--timeout=120000"]
        subprocess.run(base + [f"--screenshot={png}", url], check=True, capture_output=True)
        dom = subprocess.run(base + ["--dump-dom", url], check=True, capture_output=True, text=True).stdout
        server.shutdown()
    stats = dom.split('id="stats">')[-1].split("<")[0] if 'id="stats">' in dom else "no stats: the page did not finish"
    print(f"{png}\n{stats}")
    if "stand-ins: 0" not in stats:
        raise SystemExit("contact-sheet: some mesh files did not load, so the sheet shows their stand-ins")


main()
