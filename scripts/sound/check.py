#!/usr/bin/env python3
"""Checks the files in web/audio by numbers, because a script cannot listen. It needs ffmpeg and numpy, not the SoundFont.

For each short sound: its length, peak, loudest 50 ms, and the silence a decoder leaves at its start.
For each loop: its loudness, peak, and how well one period matches the next where the player joins them.
It fails if a file is silent or clipped, if a loop's join does not match, or if the whole folder is over 10 MB.
"""
import json, os, re, subprocess, sys
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AUDIO = os.path.join(ROOT, "web", "audio")
FFMPEG = "ffmpeg"
SR = 44100
OVERHANG = 0.25  # as in render.py and web/sound.js
MB = 1024 * 1024


def decode(path):
    raw = subprocess.run([FFMPEG, "-v", "error", "-i", path, "-f", "f32le", "-ac", "2", "-ar", str(SR), "-"], check=True, capture_output=True).stdout
    return np.frombuffer(raw, "<f4").reshape(-1, 2)


def db(x):
    return 20 * np.log10(max(float(x), 1e-9))


def loudness(path):
    r = subprocess.run([FFMPEG, "-hide_banner", "-nostats", "-i", path, "-af", "ebur128=peak=true", "-f", "null", "-"], capture_output=True, text=True).stderr
    tail = r[r.rfind("Summary:"):]
    return float(re.search(r"I:\s+(-?[\d.]+) LUFS", tail).group(1)), float(re.search(r"Peak:\s+(-?[\d.]+) dBFS", tail).group(1))


def seam(x, seconds):
    """Two numbers about the join. The player goes from `end` back to `start`.

    The first says how far apart the two sides are, in dB under the music. A lossy file never matches itself exactly,
    so this is about the size of the codec's own noise. The second is what would be heard as a click: the step
    from the last sample before the join to the first after it, as a share of the largest step just around it."""
    start, end = int(OVERHANG * SR), int((OVERHANG + seconds) * SR)
    w = 2048
    a, b = x[start - w:start + w], x[end - w:end + w]
    k = min(len(a), len(b))
    a, b = a[:k], b[:k]
    apart = db(np.sqrt(((a - b) ** 2).mean())) - db(np.sqrt((a ** 2).mean()))
    steps = max(np.abs(np.diff(x[end - 4000:end], axis=0)).max(), np.abs(np.diff(x[start:start + 4000], axis=0)).max())
    return apart, float(np.abs(x[start] - x[end - 1]).max() / max(steps, 1e-9))


def main():
    bad = []
    total = 0
    print(f"{'short sound':16} {'ms':>5} {'peak':>6} {'loud50':>7} {'lead ms':>7} {'KB':>5}")
    for f in sorted(os.listdir(os.path.join(AUDIO, "fx"))):
        path = os.path.join(AUDIO, "fx", f)
        total += os.path.getsize(path)
        x = decode(path)
        mono = x.mean(axis=1)
        over = np.nonzero(np.abs(mono) > .002)[0]
        w = int(.05 * SR)
        loud = max(np.sqrt((mono[i:i + w] ** 2).mean()) for i in range(0, max(1, len(mono) - w), w // 2))
        peak = np.abs(x).max()
        print(f"{f[:-4]:16} {len(x) / SR * 1000:5.0f} {db(peak):6.1f} {db(loud):7.1f} {(over[0] / SR * 1000 if len(over) else -1):7.1f} {os.path.getsize(path) / 1024:5.1f}")
        if peak < .1:
            bad.append(f"{f} is nearly silent")
        if peak >= .999:
            bad.append(f"{f} clips")
    lengths = json.load(open(os.path.join(AUDIO, "music", "tracks.json")))
    print(f"\n{'loop':12} {'seconds':>8} {'LUFS':>6} {'peak':>6} {'join dB':>8} {'step':>5} {'KB':>6}")
    for name, seconds in lengths.items():
        path = os.path.join(AUDIO, "music", f"{name}.mp3")
        total += os.path.getsize(path)
        x = decode(path)
        lufs, peak = loudness(path)
        join, step = seam(x, seconds)
        print(f"{name:12} {seconds:8.2f} {lufs:6.1f} {peak:6.1f} {join:8.1f} {step:5.2f} {os.path.getsize(path) / 1024:6.0f}")
        if join > -12:
            bad.append(f"{name}: the two sides of its join differ too much ({join:.1f} dB)")
        if step > 1:
            bad.append(f"{name}: the step across its join is larger than any step around it")
        if peak >= -.5:
            bad.append(f"{name} peaks too high")
    print(f"\nTotal {total / MB:.2f} MB")
    if total > 10 * MB:
        bad.append("the audio is over 10 MB")
    for b in bad:
        print("FAILED:", b)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
