#!/usr/bin/env python3
"""The trailer's score, on the edit's own beat grid.

The strings and the rest of the orchestra come from a SoundFont (MuseScore General, MIT), played by fluidsynth
from MIDI files written here. Numpy adds what no orchestra plays: the slime, the synth pulse, the creaking wood,
and the short sounds of the game: a die, a stamp, a piece landing, the seal. Every note is also written to
score.txt with a check of its harmony and range, so that the score can be read when it cannot be heard.
"""
import hashlib, os, re, subprocess, wave
import numpy as np

SR = 44100
FFMPEG = "/opt/homebrew/bin/ffmpeg"
FLUID = "/opt/homebrew/bin/fluidsynth"
PPQ = 480
rng = np.random.default_rng(1234)
NAMES = "C C# D Eb E F F# G G# A Bb B".split()
MODE = {2, 4, 5, 7, 9, 10, 11, 0}  # D Aeolian with Dorian's B natural: D E F G A Bb/B C
# Programs in General MIDI. Each has a playable range, for the check.
VIOLIN, FIDDLE, STRINGS, TREMOLO, CELLO, BASS, PIZZ, HORN, TUBA, BASSOON, ACCORDION, GUITAR, TIMPANI, TAIKO = 40, 110, 48, 44, 42, 43, 45, 60, 58, 70, 21, 24, 47, 116
RANGE = {VIOLIN: (55, 100), FIDDLE: (55, 100), STRINGS: (36, 96), TREMOLO: (36, 96), CELLO: (36, 76), BASS: (28, 60), PIZZ: (40, 96), HORN: (41, 77), TUBA: (28, 58),
         BASSOON: (34, 72), ACCORDION: (48, 84), GUITAR: (40, 84), TIMPANI: (36, 57), TAIKO: (30, 60)}
PROGRAM = {v: k for k, v in dict(violin=VIOLIN, fiddle=FIDDLE, strings=STRINGS, tremolo=TREMOLO, cello=CELLO, bass=BASS, pizz=PIZZ, horn=HORN, tuba=TUBA, bassoon=BASSOON,
                                 accordion=ACCORDION, guitar=GUITAR, timpani=TIMPANI, taiko=TAIKO).items()}
PAN = {VIOLIN: 64, FIDDLE: 70, STRINGS: 54, TREMOLO: 54, CELLO: 80, BASS: 72, PIZZ: 46, HORN: 40, TUBA: 78, BASSOON: 56, ACCORDION: 88, GUITAR: 36, TIMPANI: 58, TAIKO: 64}
# Chords as pitch classes.
D_MIN, B_FLAT, C_MAJ, F_MAJ, G_MIN, G_MAJ, A_MAJ, E_FLAT, D_MAJ = {2, 5, 9}, {10, 2, 5}, {0, 4, 7}, {5, 9, 0}, {7, 10, 2}, {7, 11, 2}, {9, 1, 4}, {3, 7, 10}, {2, 6, 9}


class Score:
    """Notes in beats, kept per stem. Each stem becomes one MIDI file, and one track of the mix."""

    def __init__(self, bpm):
        self.bpm, self.stems, self.chan, self.notes, self.harmony = bpm, {}, {}, [], []
        self.end = None  # the section being laid: nothing sounds past its last beat

    def channel(self, stem, prog):
        chans = self.chan.setdefault(stem, {})
        if prog not in chans:
            used = len(chans)
            ch = used if used < 9 else used + 1
            chans[prog] = ch
            ev = self.stems.setdefault(stem, [])
            ev.append((0, 0, bytes([0xC0 | ch, prog])))
            ev.append((0, 0, bytes([0xB0 | ch, 10, PAN.get(prog, 64)])))
            ev.append((0, 0, bytes([0xB0 | ch, 7, 110])))
        return chans[prog]

    def note(self, stem, prog, b, m, d, v=80, loose=0.0, part=""):
        if self.end is not None:
            if b >= self.end:
                return
            d = min(d, self.end - b)
        ch = self.channel(stem, prog)
        off = rng.uniform(-loose, loose) if loose else 0.0
        on_t, off_t = max(0, round((b + off) * PPQ)), round((b + d) * PPQ)
        v = int(np.clip(v, 1, 127))
        ev = self.stems[stem]
        ev.append((on_t, 2, bytes([0x90 | ch, m, v])))
        ev.append((off_t, 1, bytes([0x80 | ch, m, 0])))
        self.notes.append((b, stem, prog, m, d, v, part))

    def cc(self, stem, prog, n, b0, b1, v0, v1, step=0.125):
        ch = self.channel(stem, prog)
        for i in range(max(1, int((b1 - b0) / step)) + 1):
            t = i / max(1, int((b1 - b0) / step))
            self.stems[stem].append((round((b0 + (b1 - b0) * t) * PPQ), 0, bytes([0xB0 | ch, n, int(np.clip(v0 + (v1 - v0) * t, 0, 127))])))

    def droop(self, stem, prog, b, d, semis=1.2):
        """A pitch that sags through a note: this is what makes the melody slimy."""
        ch = self.channel(stem, prog)
        for i in range(9):
            val = int(8192 - 8191 * (semis / 2) * (i / 8) ** 1.5)
            self.stems[stem].append((round((b + d * i / 8) * PPQ), 0, bytes([0xE0 | ch, val & 127, val >> 7])))
        self.stems[stem].append((round((b + d) * PPQ), 0, bytes([0xE0 | ch, 0, 64])))

    def drum(self, b, key, v=90, part="drums"):
        if self.end is not None and b >= self.end:
            return
        ev = self.stems.setdefault("drums", [])
        t = max(0, round(b * PPQ))
        ev.append((t, 2, bytes([0x99, key, int(np.clip(v, 1, 127))])))
        ev.append((t + 60, 1, bytes([0x89, key, 0])))
        self.notes.append((b, "drums", -1, key, 0.1, v, part))

    def chord_name(self, b, pcs, name):
        self.harmony.append((b, pcs, name))


def write_midi(path, events, bpm):
    tempo = round(60e6 / bpm)
    data = bytearray([0, 0xFF, 0x51, 3, tempo >> 16 & 255, tempo >> 8 & 255, tempo & 255])
    last = 0
    for t, _, msg in sorted(events, key=lambda e: (e[0], e[1])):
        d = t - last
        last = t
        buf = [d & 127]
        d >>= 7
        while d:
            buf.insert(0, (d & 127) | 128)
            d >>= 7
        data += bytes(buf) + msg
    data += bytes([0, 0xFF, 0x2F, 0])
    with open(path, "wb") as f:
        f.write(b"MThd" + (6).to_bytes(4, "big") + (0).to_bytes(2, "big") + (1).to_bytes(2, "big") + PPQ.to_bytes(2, "big"))
        f.write(b"MTrk" + len(data).to_bytes(4, "big") + bytes(data))


def render_stem(events, bpm, sf, folder, stem, length):
    """One stem through fluidsynth, dry. Kept while its notes stay the same."""
    os.makedirs(folder, exist_ok=True)
    mid = os.path.join(folder, stem + ".mid")
    write_midi(mid, events, bpm)
    with open(mid, "rb") as f:
        key = hashlib.sha256(f.read()).hexdigest()[:12]
    out = os.path.join(folder, f"{stem}-{key}.wav")
    if not os.path.exists(out):
        subprocess.run([FLUID, "-ni", "-g", "0.6", "-r", str(SR), "-o", "synth.reverb.active=0", "-o", "synth.chorus.active=0", "-o", "synth.polyphony=512", "-F", out, sf, mid],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    with wave.open(out) as w:
        x = np.frombuffer(w.readframes(w.getnframes()), "<i2").reshape(-1, 2) / 32768
    y = np.zeros((length, 2))
    n = min(length, len(x))
    y[:n] = x[:n]
    return y


# ---------------------------------------------------------------- the themes, as (beat, note, length)
D4, E4, F4, G4, A4, Bb4, B4, C5, D5, E5, F5, G5, A5, Bb5, C6, D6, E6, F6, G6, A6 = 62, 64, 65, 67, 69, 70, 71, 72, 74, 76, 77, 79, 81, 82, 84, 86, 88, 89, 91, 93
THEME_TURN = [(0, F5, 2), (2, G5, 1), (3, A5, 1), (4, A5, 1.5), (5.5, G5, .5), (6, F5, 1), (7, E5, 1), (8, D5, 1), (9, F5, 1), (10, E5, 1), (11, C5, 1), (12, D5, 4)]
THEME_HIGH = [(0, A5, 2), (2, D6, 1), (3, E6, 1), (4, F6, 3), (7, E6, .5), (7.5, D6, .5), (8, C6, 1.5), (9.5, D6, .5), (10, E6, 1), (11, C6, 1), (12, D6, 2), (14, A5, 2),
              (16, D6, 1), (17, F6, 1), (18, G6, 1), (19, A6, 1), (20, A6, 4)]
# The same opening, for the pizzicato: the melody goes slimy.
THEME_SLIME = [(0, A4, 1), (1, D5, .5), (1.5, D5, .5), (2, E5, 1), (3, F5, 1), (4, F5, 1), (5, E5, .5), (5.5, D5, .5), (6, C5, 1), (7, D5, 1), (8, E5, 1), (9, C5, 1), (10, D5, 2)]
# A hornpipe in D Dorian, built on the same rising fourth. Eighth notes, swung.
HORNPIPE = [D5, F5, A5, F5, D6, A5, F5, A5, G5, B4 + 12, D6, B4 + 12, A5, G5, F5, E5, D5, F5, A5, D6, C6, A5, G5, E5]


def violin_line(s, a, phrase, v=92, stem="solo", prog=VIOLIN, double=None, part="melody"):
    """A solo line: each long note swells and gains vibrato, and notes overlap a little, as bowed notes do."""
    for off, m, d in phrase:
        b = a + off
        s.note(stem, prog, b, m, d + 0.04, v + (6 if d >= 2 else 0), loose=0.01, part=part)
        if d >= 1:
            s.cc(stem, prog, 11, b, b + d * 0.45, 78, 118)
            s.cc(stem, prog, 11, b + d * 0.45, b + d, 118, 92)
            s.cc(stem, prog, 1, b + 0.2, b + min(d, 1), 10, 70)
        else:
            s.cc(stem, prog, 11, b, b + d, 100, 100, step=d)
        if double is not None:
            s.note("strings", STRINGS, b, m, d + 0.04, double, loose=0.012, part="doubling")


def pad(s, b, d, notes, v=55, prog=STRINGS, stem="strings", swell=(70, 110), part="pad"):
    for m in notes:
        s.note(stem, prog, b, m, d, v, loose=0.01, part=part)
    s.cc(stem, prog, 11, b, b + d * 0.6, swell[0], swell[1])
    s.cc(stem, prog, 11, b + d * 0.6, b + d, swell[1], swell[1] * 0.8)


def ostinato(s, b, bars, roots, v=66):
    """The drive of the string section: cellos on a long-short-short eighth-note figure, basses on the root."""
    for i in range(bars * 8):
        t = b + i / 2
        root = roots[(i // 8) % len(roots)]
        hit = i % 8 in (0, 3, 6)
        s.note("strings", CELLO, t, root + 12 + (7 if i % 8 == 6 else 0), 0.42, v + (14 if hit else 0), part="ostinato")
        if i % 4 == 0:
            s.note("strings", BASS, t, root, 1.9, v, part="bass")


def frame_drum(s, b, bars, v=80):
    """A frame drum's pattern, on the low conga and its muted note, with a light tambourine."""
    for i in range(bars):
        for off, key, g in ((0, 64, 1.0), (1.5, 64, .75), (2, 64, .9), (3, 63, .7), (3.5, 64, .8)):
            s.drum(b + i * 4 + off, key, v * g, "frame drum")
        for off in (1, 3):
            s.drum(b + i * 4 + off, 54, v * .35, "tambourine")


def timp(s, b, m=38, v=95, roll=0, part="timpani"):
    """One timpani stroke, or a roll of this many beats that grows into the next stroke."""
    if roll:
        n = int(roll * 4)
        for i in range(n):
            s.note("perc", TIMPANI, b + i / 4, m, 0.3, v * (0.4 + 0.6 * i / n), part="timpani roll")
    else:
        s.note("perc", TIMPANI, b, m, 1.2, v, part=part)


def lay_open(s, a, n):
    """Four beats: a drone and a solo violin climbing the rising fourth, then straight into the game."""
    s.chord_name(a, D_MIN, "Dm")
    s.note("strings", BASS, a, 38, n, 62, part="drone")
    s.note("strings", CELLO, a, 50, n, 54, part="drone")
    s.cc("strings", CELLO, 11, a, a + 3, 60, 110)
    s.note("strings", CELLO, a + 1, 57, n - 1, 50, part="drone")
    timp(s, a, 38, 70)
    timp(s, a + 2, 38, 104)
    violin_line(s, a, [(0, A4, 1), (1, D5, 1), (2, E5, 1), (3, F5, 1)], 94)


def lay_game(s, a, n):
    for b, c, name in ((0, F_MAJ, "F"), (2, C_MAJ, "C"), (4, F_MAJ, "F"), (6, C_MAJ, "C"), (8, B_FLAT, "Bb"), (10, C_MAJ, "C")):
        s.chord_name(a + b, c, name)
    violin_line(s, a, [x for x in THEME_TURN if x[0] < n], 100, double=64)
    for b, d, notes in ((0, 2, [53, 60, 65]), (2, 2, [55, 60, 64]), (4, 2, [53, 60, 65]), (6, 2, [55, 60, 64]), (8, 2, [53, 58, 62]), (10, 2, [55, 60, 64])):
        pad(s, a + b, d, notes, 58)
    ostinato(s, a, 2, [41], 66)
    ostinato(s, a + 8, 1, [34], 70)
    frame_drum(s, a, 3)
    timp(s, a, 41, 100)
    timp(s, a + 8, 46, 95)
    for i in range(n * 2):  # a plucked gut string in eighths: an old sound, and a quiet one
        c = [65, 72, 77, 72, 67, 72, 76, 72, 65, 72, 77, 72, 67, 72, 76, 72, 65, 70, 74, 70, 67, 72, 76, 72][i % 24]
        s.note("pluck", GUITAR, a + i / 2, c, 0.9, 58 + (10 if i % 4 == 0 else 0), loose=0.01, part="gut string")


def lay_rule(s, a, n, hits):
    """Tight and low while the rule is written. It turns dark at the vote, and the seal brings the home chord."""
    h = min(hits) if hits else a + n - 2
    dark = h - 3
    s.chord_name(a, D_MIN, "Dm")
    s.chord_name(a + 4, G_MIN, "Gm")
    s.chord_name(dark, A_MAJ, "A")
    s.chord_name(h, D_MIN, "Dm")
    pad(s, a, 4, [50, 57, 62, 65], 56, TREMOLO, swell=(60, 90))
    pad(s, a + 4, dark - a - 4, [50, 55, 62, 67], 60, TREMOLO, swell=(70, 100))
    pad(s, dark, h - dark, [45, 52, 57, 61, 64, 69], 70, TREMOLO, swell=(70, 127), part="tension")
    for i in range(int((h - a) * 2)):
        t = a + i / 2
        root = 38 if t < a + 4 else 43 if t < dark else 45
        s.note("strings", CELLO, t, root + 12, 0.4, 60 + 2 * i, part="pulse")
    for i in range(int((dark - a) * 2)):  # keystrokes, as high pizzicato
        s.note("pluck", PIZZ, a + i / 2, [74, 77, 81, 77][i % 4] if i < 8 else [79, 82, 86, 82][i % 4], 0.3, 52 + i, loose=0.015, part="keys")
    s.note("solo", VIOLIN, a, A5, 4, 76, part="held")
    s.cc("solo", VIOLIN, 11, a, a + 4, 60, 105)
    s.note("solo", VIOLIN, a + 4, Bb5, dark - a - 4, 84, part="held")
    s.cc("solo", VIOLIN, 11, a + 4, dark, 70, 110)
    s.note("solo", VIOLIN, dark, A5, h - dark, 92, part="held")
    s.cc("solo", VIOLIN, 11, dark, h, 80, 127)
    timp(s, dark, 45, 104, roll=h - dark)
    # The seal: the whole section on the home chord, and the theme's first rise.
    timp(s, h, 38, 127)
    s.note("perc", TAIKO, h, 41, 1.5, 120, part="seal")
    for m in (38, 50, 57, 62, 65, 69, 74):
        s.note("strings", STRINGS, h, m, a + n - h, 88, part="seal chord")
    s.cc("strings", STRINGS, 11, h, h + 1, 127, 92)
    violin_line(s, h, [(o, m, d) for o, m, d in [(0, D6, 1), (1, F6, 1)] if h + o < a + n], 100)


def lay_evolve(s, a, n):
    for b, c, name in ((0, D_MIN, "Dm"), (4, B_FLAT, "Bb"), (8, C_MAJ, "C"), (12, A_MAJ, "A")):
        s.chord_name(a + b, c, name)
    phrase = [x for x in THEME_HIGH if x[0] < 12] + [(12, A5, 1), (13, 85, 1), (14, E6, 1), (15, A6, 1)]
    violin_line(s, a, phrase, 110, double=80)
    for o, m, d in phrase:  # the section an octave below, so the tune stands on something
        s.note("strings", STRINGS, a + o, m - 12, d + 0.04, 76, loose=0.012, part="octave")
    for b, notes, root in ((0, [50, 57, 62, 65], 38), (4, [46, 53, 58, 62], 34), (8, [48, 55, 60, 64], 36), (12, [45, 52, 57, 61], 33)):
        pad(s, a + b, 4, notes, 72)
        ostinato(s, a + b, 1, [root], 72 + (b // 2))
        s.note("winds", HORN, a + b, notes[1] + 12 if notes[1] < 60 else notes[1], 4, 58 + b // 2, loose=0.01, part="horns")
        s.note("winds", HORN, a + b, notes[2] + 12 if notes[2] < 60 else notes[2], 4, 54 + b // 2, loose=0.01, part="horns")
    frame_drum(s, a, 4, 92)
    for i in range(0, n, 4):
        timp(s, a + i, {0: 38, 4: 46, 8: 48, 12: 45}.get(i, 38), 108)
        s.note("perc", TAIKO, a + i, 41, 1.2, 92 + i, part="taiko")
        s.note("perc", TAIKO, a + i + 2.5, 41, 0.8, 74 + i, part="taiko")
        s.note("perc", TAIKO, a + i + 3, 41, 0.8, 80 + i, part="taiko")
    timp(s, a + n - 4, 45, 112, roll=4)
    pad(s, a + n - 4, 4, [69, 73, 76, 81], 84, TREMOLO, swell=(80, 127), part="tension")


def lay_slime(s, a, n):
    """The same melody, gone wet: pizzicato that sags, a tuba underneath. The squelches are in `layers`."""
    for k in range(0, n, 12):
        for b, c, name in ((0, D_MIN, "Dm"), (8, C_MAJ, "C"), (10, D_MIN, "Dm")):
            if k + b < n:
                s.chord_name(a + k + b, c, name)
        for off, m, d in THEME_SLIME:
            if k + off >= n:
                break
            b = a + k + off
            s.note("pluck", PIZZ, b, m, min(d, 0.8), 104, part="melody")
            s.droop("pluck", PIZZ, b, min(d, 0.8))
            s.note("winds", BASSOON, b, m - 12, min(d, 0.45) * 0.8, 62, part="bassoon")
    for i in range(n):
        j = i % 12
        s.note("winds", TUBA, a + i, (38 if j % 4 < 2 else 45) if j < 8 else (36 if j < 10 else 38), 0.42, 72 if i % 2 == 0 else 48, part="tuba")
    timp(s, a, 38, 122)
    s.note("perc", TAIKO, a, 41, 1.5, 118, part="big beat")


def lay_strike(s, a, n):
    """Low horns and bass under the same fourth, as dwarves would play it. The anvil and the rock are in `layers`."""
    s.chord_name(a, D_MIN, "Dm")
    s.chord_name(a + 4, B_FLAT, "Bb")
    for i in range(n):
        root = 38 if i < 4 else 34
        s.note("winds", TUBA, a + i, root, 0.8, 92 if i % 2 == 0 else 70, part="bass")
        s.note("strings", BASS, a + i, root, 0.8, 84, part="bass")
    for off, m, d in ((0, 57, 1), (1, 62, 1), (2, 64, 1), (3, 65, 3)):
        s.note("winds", HORN, a + off, m, d, 104, part="melody")
        s.note("winds", HORN, a + off, m - 7 if m - 7 >= 41 else m, d, 86, part="horn fifth")
    timp(s, a, 38, 118)
    s.note("perc", TAIKO, a, 41, 1.5, 116, part="big beat")
    for i in range(0, n, 2):
        s.note("perc", TAIKO, a + i + 1, 41, 0.8, 92, part="taiko")


def lay_bubble(s, a, n, burst):
    """Glass strings climbing a half step at a time over the synth pulse. It bursts on the audit, then climbs again."""
    head = burst - a
    for b, up in ((0, 0), (4, 1), (8, 2)):
        if b >= head:
            break
        s.chord_name(a + b, {2 + up, 5 + up, 9 + up}, ["Dm", "Ebm", "Em"][up])
        for m in (74, 77, 81, 86):
            s.note("glass", TREMOLO, a + b, m + up, min(4, head - b), 60 + 14 * up, part="glass")
        s.cc("glass", TREMOLO, 11, a + b, a + min(head, b + 4), 70 + 12 * up, 100 + 13 * up)
    for off, m, d in ((0, 86, 2), (2, 89, 2), (4, 90, 2), (6, 91, 2), (8, 92, 1), (9, 93, 1), (10, 94, .5), (10.5, 95, .5), (11, 96, 1)):
        if a + off < burst:
            s.note("glass", VIOLIN, a + off, m, min(d, burst - a - off), 100, part="glass melody")
    # The burst: everything at once, on the audit's cut.
    s.chord_name(burst, D_MIN, "Dm")
    timp(s, burst, 38, 127)
    s.note("perc", TAIKO, burst, 41, 1.5, 124, part="burst")
    for m in (38, 50, 57, 62, 65, 69, 74, 77):
        s.note("strings", STRINGS, burst, m, 0.9, 110, part="burst chord")
    # After it, the bubble fills again: the same glass, thinner, a half step higher each two bars.
    k = 0
    for b in range(burst + 2, a + n, 4):
        s.chord_name(b, {2 + k, 5 + k, 9 + k}, ["Dm", "Ebm", "Em", "Fm"][k % 4])
        for m in (74, 81):
            s.note("glass", TREMOLO, b, m + k, min(4, a + n - b), 60 + 10 * k, part="glass")
        k += 1


def lay_pirate(s, a, n):
    """A fast fiddle hornpipe with stomps and a squeezebox. Same tempo, same mode, a different ship."""
    for k in range(0, n, 12):
        for b, c, name in ((0, D_MIN, "Dm"), (4, G_MAJ, "G"), (6, D_MIN, "Dm"), (10, C_MAJ, "C")):
            if k + b < n:
                s.chord_name(a + k + b, c, name)
    for i in range(n * 2):
        m = HORNPIPE[i % len(HORNPIPE)]
        swing = 0.08 if i % 2 else 0.0
        s.note("solo", FIDDLE, a + i / 2 + swing, m, 0.46, 112 if i % 2 == 0 else 96, part="hornpipe")
    for i in range(n):
        j = i % 12
        s.drum(a + i, 36 if i % 2 == 0 else 39, 100 if i % 2 == 0 else 74, "stomp and clap")
        root, chord = ((38, [62, 65, 69]) if j < 4 or 6 <= j < 10 else (43, [62, 67, 71]) if j < 6 else (36, [60, 64, 67]))
        s.note("winds", TUBA, a + i, root if i % 2 == 0 else root + 7, 0.4, 62, part="bass")
        for m in chord:
            s.note("winds", ACCORDION, a + i + 0.5, m, 0.34, 60, part="squeezebox")
    timp(s, a, 38, 110)


def lay_flash(s, a, n):
    stabs = (([38, 50, 57, 62, 65], D_MIN, "Dm"), ([34, 46, 53, 58, 62], B_FLAT, "Bb"), ([36, 48, 55, 60, 64], C_MAJ, "C"), ([33, 45, 52, 57, 61], A_MAJ, "A"))
    for i, (notes, c, name) in enumerate(stabs[-n:]):
        s.chord_name(a + i, c, name)
        for m in notes:
            s.note("strings", BASS if m < 36 else STRINGS, a + i, m, 0.9, 104, part="stab")
        s.note("solo", VIOLIN, a + i, [D6, D6, E6, A5][4 - n + i], 0.9, 110, part="stab")
        timp(s, a + i, notes[0] + 12 if notes[0] < 36 else notes[0], 116)
        s.note("perc", TAIKO, a + i, 41, 0.8, 112, part="taiko")


def lay_resolve(s, a, n, url):
    b = url["start_beat"]
    s.chord_name(a, D_MIN, "Dm")
    s.chord_name(a + 4, B_FLAT, "Bb")
    s.chord_name(a + 6, C_MAJ, "C")
    s.chord_name(b, D_MAJ, "D")
    pad(s, a, 4, [38, 50, 57, 62, 65], 60)
    pad(s, a + 4, 2, [46, 53, 58, 62], 60)
    pad(s, a + 6, b - a - 6, [48, 55, 60, 64], 64)
    violin_line(s, a, [(0, A5, 2), (2, D6, 1), (3, E6, 1), (4, F6, 2), (6, E6, 1), (7, C6, 1)], 92)
    timp(s, a, 38, 92)
    # The address: D major, the only major D in the piece, held to the end.
    timp(s, b, 38, 118)
    s.note("perc", TAIKO, b, 41, 2, 100, part="last beat")
    for m in (38, 50, 57, 62, 66, 69, 74, 78):
        s.note("strings", STRINGS, b, m, url["beats"], 84, part="held chord")
    s.cc("strings", STRINGS, 11, b, b + url["beats"], 118, 96)
    s.note("winds", HORN, b, 62, url["beats"], 70, part="held chord")
    s.note("winds", HORN, b, 69, url["beats"], 66, part="held chord")
    violin_line(s, b, [(0, D6, url["beats"])], 96)


# ---------------------------------------------------------------- what numpy adds
def lowpass(x, cut):
    X = np.fft.rfft(x)
    f = np.fft.rfftfreq(len(x), 1 / SR)
    X *= np.clip((cut * 1.3 - f) / (cut * 0.3), 0, 1)
    return np.fft.irfft(X, len(x))


def band(x, lo, hi):
    X = np.fft.rfft(x)
    f = np.fft.rfftfreq(len(x), 1 / SR)
    X *= np.clip((f - lo * 0.7) / (lo * 0.3 + 1), 0, 1) * np.clip((hi * 1.3 - f) / (hi * 0.3), 0, 1)
    return np.fft.irfft(X, len(x))


def decay(n, rate):
    return np.exp(-np.arange(n) / SR * rate)


def glide(f0, f1, dur, shape=1.5):
    n = int(dur * SR)
    t = np.linspace(0, 1, n)
    return np.sin(2 * np.pi * np.cumsum(f0 + (f1 - f0) * t ** shape) / SR)


def resonate(x, freqs, rate):
    """Noise or a click, ringing at these frequencies, as wood does."""
    t = np.arange(len(x)) / SR
    ir = sum(np.sin(2 * np.pi * f * t) * np.exp(-t * rate * (1 + i * .4)) for i, f in enumerate(freqs))
    return np.fft.irfft(np.fft.rfft(x, len(x) * 2) * np.fft.rfft(ir, len(x) * 2))[: len(x)]


def bubble_pop():
    d = rng.uniform(.03, .09)
    f = rng.uniform(280, 1000)
    x = glide(f, f * rng.uniform(1.6, 2.6), d)
    return x * np.hanning(len(x)) * rng.uniform(.3, 1)


def squelch():
    d = rng.uniform(.14, .26)
    n = int(d * SR)
    wet = glide(rng.uniform(520, 760), rng.uniform(90, 150), d, 0.7) * (1 + .5 * np.sin(np.arange(n) / SR * 2 * np.pi * rng.uniform(30, 55)))
    return (np.tanh(2 * wet) + 0.5 * lowpass(rng.uniform(-1, 1, n), 1800) * decay(n, 18)) * np.hanning(n) ** .5


def creak():
    d = rng.uniform(.5, .8)
    n = int(d * SR)
    x = np.zeros(n)
    t, rate = 0.0, rng.uniform(26, 48)
    while t < d:
        x[min(n - 1, int(t * SR))] = rng.uniform(.5, 1)
        t += 1 / max(10, rate + 14 * np.sin(t * 12) + rng.uniform(-6, 6))
    return resonate(x, [rng.uniform(640, 820), rng.uniform(1250, 1500), 2300], 36) * np.hanning(n) ** .5


def cold_pulse(m, dur, cut):
    t = np.arange(int(dur * SR)) / SR
    f = 440 * 2 ** ((m - 69) / 12)
    x = 2 * ((f * t) % 1) - 1
    x += 2 * ((f * 1.005 * t) % 1) - 1
    return lowpass(x, cut) * decay(len(t), 9) * np.minimum(1, t / .003) * .5


def riser(dur):
    n = int(dur * SR)
    t = np.linspace(0, 1, n)
    x = band(rng.uniform(-1, 1, n), 1800, 14000) * t ** 2.4
    for k in (0, 1, 2):  # several octaves climbing together: it seems to rise and never arrive
        x += np.sin(2 * np.pi * np.cumsum(110 * 2 ** k * 2 ** (2.6 * t)) / SR) * t ** 1.8 * .4
    return x


def impact():
    n = int(2.4 * SR)
    t = np.arange(n) / SR
    return np.tanh(1.6 * np.sin(2 * np.pi * np.cumsum(32 + 70 * np.exp(-t * 9)) / SR)) * np.exp(-t * 2) + band(rng.uniform(-1, 1, n), 700, 12000) * np.exp(-t * 5) * .5


def fx_die():
    n = int(.34 * SR)
    x = np.zeros(n)
    for at, g in ((0, 1), (.055, .7), (.1, .5), (.15, .34), (.21, .2)):
        x[int(at * SR)] = g
    return resonate(x + rng.uniform(-.004, .004, n), [1900, 3100, 760], 70)


def fx_stamp():
    n = int(.2 * SR)
    thud = glide(170, 70, .2, .6) * decay(n, 24)
    slap = band(rng.uniform(-1, 1, n), 500, 7000) * decay(n, 60)
    return thud + .7 * slap


def fx_seal():
    n = int(.5 * SR)
    thud = glide(120, 42, .5, .5) * decay(n, 10)
    wax = band(rng.uniform(-1, 1, n), 200, 2600) * decay(n, 30) * .7
    return thud + wax


def fx_piece():
    n = int(.14 * SR)
    x = np.zeros(n)
    x[0], x[int(.018 * SR)] = 1, .5
    return resonate(x, [520, 1150, 2050], 60)


def fx_coins():
    n = int(.42 * SR)
    x = np.zeros(n)
    for at, g in ((0, 1), (.05, .75), (.11, .6), (.18, .45), (.27, .3)):
        k = int(at * SR)
        x[k:k + int(.14 * SR)] += g * resonate(np.eye(1, int(.14 * SR)).ravel(), [rng.uniform(3000, 3400), rng.uniform(4500, 5100), rng.uniform(6800, 7600)], 60)
    return x


def fx_cards():
    n = int(.24 * SR)
    return band(rng.uniform(-1, 1, n), 1200, 7000) * np.sin(np.linspace(0, np.pi, n)) ** 2 * .9


def fx_crash():
    """The bubble goes: the low hit and a spray of glass."""
    x = impact()
    glass = np.zeros(int(.9 * SR))
    for _ in range(46):
        at, d = int(rng.uniform(0, .6) * SR), int(rng.uniform(.03, .14) * SR)
        ping = np.sin(2 * np.pi * rng.uniform(2600, 9000) * np.arange(d) / SR) * decay(d, 40) * rng.uniform(.25, .8)
        glass[at:at + d] += ping[: len(glass) - at]
    x[: len(glass)] += glass * .55
    return x


def fx_cannon():
    n = int(1.4 * SR)
    t = np.arange(n) / SR
    boom = np.sin(2 * np.pi * np.cumsum(38 + 110 * np.exp(-t * 16)) / SR) * np.exp(-t * 3.2)
    return np.tanh(2.2 * boom) + lowpass(rng.uniform(-1, 1, n), 1500) * np.exp(-t * 9) * 1.2 + band(rng.uniform(-1, 1, n), 2000, 9000) * np.exp(-t * 34) * .6


def fx_rumble():
    """The roof comes down: rock on rock, low and long, with stones in it."""
    n = int(1.9 * SR)
    t = np.arange(n) / SR
    roar = lowpass(rng.uniform(-1, 1, n), 170) * 5 * np.minimum(1, t / .05) * np.exp(-t * 1.3) * (1 + .4 * np.sin(2 * np.pi * 7 * t))
    stones = np.zeros(n)
    for _ in range(26):
        at, d = int(rng.uniform(0, 1.3) * SR), int(.09 * SR)
        stones[at:at + d] += rng.uniform(.15, .55) * glide(rng.uniform(120, 320), 60, .09, .5) * decay(d, 40)
    return np.tanh(roar) + stones


def fx_anvil():
    n = int(.3 * SR)
    return resonate(np.eye(1, n).ravel() + rng.uniform(-.01, .01, n), [1500, 2650, 3950], 22)


def fx_splat():
    n = int(.5 * SR)
    return sum(np.pad(squelch(), (int(at * SR), n))[:n] * g for at, g in ((0, 1), (.06, .7), (.16, .5)))


def fx_buzz():
    """A neon tube striking: mains hum in hard bursts, as the letters catch."""
    n = int(.62 * SR)
    t = np.arange(n) / SR
    hum = np.tanh(4 * (np.sin(2 * np.pi * 120 * t) + .6 * np.sin(2 * np.pi * 240 * t) + .4 * np.sin(2 * np.pi * 360 * t)))
    gate = np.ones(n)
    for a, b in ((.05, .09), (.13, .16), (.2, .22), (.42, .46)):
        gate[int(a * SR):int(b * SR)] = .05
    return (hum + band(rng.uniform(-1, 1, n), 3000, 9000) * .5) * gate * np.minimum(1, (n - np.arange(n)) / (.05 * SR))


def fx_slam():
    """Stone letters landing, one after another."""
    n = int(.6 * SR)
    x = np.zeros(n)
    for at, g in ((0, .9), (.05, .6), (.1, .8), (.16, .7), (.22, 1)):
        k, d = int(at * SR), int(.16 * SR)
        x[k:k + d] += g * (glide(150, 48, .16, .5)[:d] * decay(d, 22) + band(rng.uniform(-1, 1, d), 400, 3000) * decay(d, 60) * .6)
    return x


def fx_keys():
    """Fingers on the keys, for the length of the typing."""
    n = int(2.2 * SR)
    x = np.zeros(n)
    t = 0.05
    while t < 2.1:
        k = int(t * SR)
        d = int(.02 * SR)
        x[k:k + d] += band(rng.uniform(-1, 1, d), 1800, 9000) * decay(d, 240) * rng.uniform(.5, 1)
        t += rng.uniform(.045, .09)
    return x


CUES = {"splat": fx_splat, "buzz": fx_buzz, "slam": fx_slam, "keys": fx_keys, "seal": fx_seal, "coins": fx_coins, "cards": fx_cards, "crash": fx_crash, "cannon": fx_cannon, "rumble": fx_rumble}


def fx_for(kind, slot):
    if kind == "die":
        return fx_die(), .5
    if kind == "stamp":
        return fx_stamp(), .9
    if kind == "seal":
        return fx_seal(), 1.0
    if slot == "slime":
        return squelch(), .35
    if slot == "bubble":
        return glide(2400, 3200, .05) * np.hanning(int(.05 * SR)), .12
    return fx_piece(), .4


def layers(s, tl, n, beat):
    """The numpy tracks: the slime, the synth pulse, the wood, the big hits and the game's own sounds."""
    y = np.zeros((n, 2))
    wet = np.zeros((n, 2))

    def put(b, x, g=1.0, pan=0.0, send=.2):
        at = int(b * beat * SR)
        if at >= n or at < 0:
            return
        x = x[: n - at]
        l, r = np.cos((pan + 1) * np.pi / 4), np.sin((pan + 1) * np.pi / 4)
        y[at:at + len(x), 0] += g * l * x
        y[at:at + len(x), 1] += g * r * x
        wet[at:at + len(x), 0] += send * g * l * x
        wet[at:at + len(x), 1] += send * g * r * x

    groups = {}
    for sh in tl["shots"]:
        if sh.get("slot"):
            groups.setdefault(sh["slot"], []).append(sh)
    for slot, shots in groups.items():
        a, m = shots[0]["start_beat"], sum(x["beats"] for x in shots)
        if slot == "slime":
            put(a, impact(), .8, 0, .4)
            for i in range(int(m * 7)):
                put(a + rng.uniform(0, m), bubble_pop(), .13, rng.uniform(-.7, .7), .4)
            for i in range(m):
                put(a + i + .5, squelch(), .34, rng.uniform(-.4, .4), .3)
        elif slot == "bubble":
            burst = next(x["start_beat"] + x["burst"] for x in shots if x.get("burst"))
            head = burst - a
            for i in range(int(head * 2)):
                t = a + i / 2
                if t >= burst - 2:
                    break
                put(t, cold_pulse(38 + i // 8, .22, 700 + 120 * i), .34 + .02 * i, 0, .1)
            for i in range(8):  # the last two beats double, then climb
                put(burst - 2 + i / 4, cold_pulse(42 + i, .12, 2000 + 400 * i), .4 + .03 * i, .3 * np.sin(i), .1)
            put(a, riser((burst - a) * beat), .34, 0, .2)
            n2 = int(a + m - burst - 2)
            for i in range(n2 * 2):
                put(burst + 2 + i / 2, cold_pulse(38 + i // 4, .2, 500 + 240 * i), .16 + .05 * i, 0, .1)
            put(a + m - 4, riser(4 * beat), .22, 0, .2)
        elif slot == "pirate":
            for i in range(0, m, 4):
                put(a + i + 1.75, creak(), .3, rng.uniform(-.5, .5), .3)
        elif slot == "strike":
            for i in range(0, m, 2):
                put(a + i, fx_anvil(), .32, .25, .4)
    for sh in tl["shots"]:
        for c in sh.get("cues", []):
            put(sh["start_beat"] + c["f"] / tl["per_beat"], CUES[c["fx"]](), c.get("g", 1.0) * {"splat": .8, "buzz": .34, "slam": .95, "keys": .5, "seal": 1.0, "coins": .4, "cards": .5, "crash": 1.0, "cannon": .95, "rumble": .95}[c["fx"]], 0, .3)
        for b, kind, slot, quiet in sh.get("sfx", []):
            fx, g = fx_for(kind, slot)
            put(b, fx, g * quiet, 0, .15)
    return y, wet


def reverb(wet, seconds=2.2):
    n = int(seconds * SR)
    t = np.arange(n) / SR
    size = len(wet) + n
    out = np.zeros((size, 2))
    for c in range(2):
        ir = np.convolve(rng.uniform(-1, 1, n), np.ones(8) / 8, "same") * np.exp(-t * 3.2)
        ir[: int(.018 * SR)] = 0
        out[:, c] = np.fft.irfft(np.fft.rfft(wet[:, c], size) * np.fft.rfft(ir, size), size)
    return out[: len(wet)] * 0.12


def limit(x, ceiling=0.87):
    """A plain look-ahead limiter, so that the peaks stay under the ceiling without clipping."""
    block = 64
    peaks = np.abs(x).max(axis=1)
    blocks = peaks[: len(peaks) // block * block].reshape(-1, block).max(axis=1)
    blocks = np.append(blocks, peaks[len(blocks) * block:].max() if len(peaks) % block else 0)
    need = np.minimum(1.0, ceiling / np.maximum(blocks, 1e-9))
    hold = np.minimum.reduce([np.roll(need, -k) for k in range(0, 4)])
    g = hold.copy()
    a = np.exp(-block / (0.08 * SR))
    for i in range(1, len(g)):
        g[i] = min(hold[i], a * g[i - 1] + (1 - a))
    gain = np.interp(np.arange(len(x)), np.arange(len(g)) * block + block / 2, g)
    return np.clip(x * gain[:, None], -ceiling, ceiling)


def loudness(wav):
    r = subprocess.run([FFMPEG, "-hide_banner", "-nostats", "-i", wav, "-af", "ebur128=peak=true", "-f", "null", "-"], capture_output=True, text=True).stderr
    tail = r[r.rfind("Summary:"):]
    return (float(re.search(r"I:\s+(-?[\d.]+) LUFS", tail).group(1)), float(re.search(r"LRA:\s+(-?[\d.]+) LU", tail).group(1)), float(re.search(r"Peak:\s+(-?[\d.]+) dBFS", tail).group(1)))


def write_wav(path, x):
    with wave.open(path, "wb") as w:
        w.setnchannels(2)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes((np.clip(x, -1, 1) * 32767).astype("<i2").tobytes())


def compose(tl):
    beat = 60 / tl["bpm"]
    s = Score(tl["bpm"])
    sec = {}
    for sh in tl["shots"]:
        sec.setdefault(sh["section"], []).append(sh)
    span = lambda name: (sec[name][0]["start_beat"], sum(x["beats"] for x in sec[name]))
    def lay(f, name, *rest):
        at, n = span(name)
        s.end = at + n
        f(s, at, n, *rest)
    lay(lay_open, "open")
    lay(lay_game, "game")
    lay(lay_rule, "rule", [x["start_beat"] + x["hit"] for x in sec["rule"] if "hit" in x])
    lay(lay_evolve, "evolve")
    lay(lay_flash, "worlds")
    # Each world keeps its own sound for as long as its shots last, and the cut changes it at once.
    run = []
    def flush():
        if not run:
            return
        a, m, kind = run[0]["start_beat"], sum(x["beats"] for x in run), run[0]["slot"]
        s.end = a + m
        if kind == "slime":
            lay_slime(s, a, m)
        elif kind == "bubble":
            lay_bubble(s, a, m, next(x["start_beat"] + x["burst"] for x in run if x.get("burst")))
        elif kind == "pirate":
            lay_pirate(s, a, m)
        else:
            lay_strike(s, a, m)
        run.clear()
    for sh in sec["worlds2"]:
        if run and run[0]["slot"] != sh["slot"]:
            flush()
        run.append(sh)
    flush()
    lay(lay_resolve, "resolve", sec["resolve"][-1])
    s.end = None
    return s, beat


def read_score(s, tl, path):
    """Writes the score as notes, bar by bar, and checks it: range, mode, chord tones on strong beats, density."""
    out, warn = [], []
    chord_at = lambda b: next((h for h in reversed(sorted(s.harmony, key=lambda h: h[0])) if h[0] <= b), None)
    sec_of = {}
    for sh in tl["shots"]:
        for i in range(sh["beats"]):
            sec_of[sh["start_beat"] + i] = sh["section"]
    melody = {"melody", "hornpipe", "glass melody", "wrong melody"}
    strong, hits, off_mode = 0, 0, []
    per = {}
    for b, stem, prog, m, d, v, part in sorted(s.notes, key=lambda n: n[0]):
        if prog in RANGE and not RANGE[prog][0] <= m <= RANGE[prog][1]:
            warn.append(f"beat {b:.1f}: {PROGRAM[prog]} {NAMES[m % 12]}{m // 12 - 1} is out of its range")
        section = sec_of.get(int(b), "end")
        per.setdefault(section, [0, 0, 127, 0, 0.0])
        rec = per[section]
        if prog != -1:
            rec[0] += 1
            rec[2], rec[3] = min(rec[2], m), max(rec[3], m)
        rec[1] += 1
        if prog != -1 and m % 12 not in MODE:
            off_mode.append((round(b, 1), PROGRAM[prog], NAMES[m % 12], part))
        if part in melody and float(b).is_integer() and int(b) % 2 == 0 and d >= 1:
            c = chord_at(b)
            strong += 1
            if c and m % 12 in c[1]:
                hits += 1
            else:
                warn.append(f"beat {b:.1f}: melody {NAMES[m % 12]} is not in {c[2] if c else '?'} (a suspension or passing note, if it resolves)")
    out.append("Harmony: " + " ".join(f"{h[2]}@{h[0]}" for h in sorted(s.harmony, key=lambda h: h[0])))
    out.append(f"Melody on strong beats, long notes: {hits} of {strong} are chord tones.")
    outside = {}
    for b, inst, name, part in off_mode:
        outside.setdefault(f"{name} ({part})", []).append(b)
    out.append("Outside D Aeolian/Dorian: " + "; ".join(f"{k} at beats {v[0]} to {v[-1]}" for k, v in outside.items()))
    out.append("Density by section (pitched notes, all notes, lowest, highest):")
    beats_in = {}
    for sh in tl["shots"]:
        beats_in[sh["section"]] = beats_in.get(sh["section"], 0) + sh["beats"]
    for sec, r in per.items():
        if sec in beats_in:
            out.append(f"  {sec:8s} {r[0] / beats_in[sec]:5.1f} pitched per beat, {r[1] / beats_in[sec]:5.1f} all, range {NAMES[r[2] % 12]}{r[2] // 12 - 1} to {NAMES[r[3] % 12]}{r[3] // 12 - 1}")
    out.append("Warnings:" if warn else "No warnings.")
    out += ["  " + w for w in warn]
    out.append("\nMelodies, bar by bar (beat: note x length):")
    bars = {}
    for b, stem, prog, m, d, v, part in s.notes:
        if part in melody | {"held", "stab", "held chord"} and prog in (VIOLIN, FIDDLE, PIZZ):
            bars.setdefault(int(b) // 4, []).append((b, m, d, part, prog))
    for bar in sorted(bars):
        row = " ".join(f"{NAMES[m % 12]}{m // 12 - 1}x{d:g}" for b, m, d, part, prog in sorted(bars[bar]))
        c = chord_at(bar * 4)
        out.append(f"  bar {bar + 1:3d} ({sec_of.get(bar * 4, 'end'):7s}) [{c[2] if c else ''}] {PROGRAM[bars[bar][0][4]]}: {row}")
    with open(path, "w") as f:
        f.write("\n".join(out) + "\n")


def render(tl, wav, folder, sf, target=-16.0):
    s, beat = compose(tl)
    seconds = tl["total_beats"] * beat
    n = int(seconds * SR) + 1
    gains = {"solo": 1.7, "strings": .85, "pluck": 1.2, "winds": .9, "perc": .9, "drums": 1.5, "glass": 1.1}
    sends = {"solo": .5, "strings": .5, "pluck": .3, "winds": .45, "perc": .35, "drums": .2, "glass": .7}
    dry, wet = np.zeros((n, 2)), np.zeros((n, 2))
    levels = {}
    for stem, ev in s.stems.items():
        x = render_stem(ev, s.bpm, sf, folder, stem, n)
        if stem == "glass":  # sul ponticello, more or less: thin the strings to their edge, and shake them
            for c in range(2):
                x[:, c] = band(x[:, c], 1400, 11000)
            x *= (0.72 + 0.28 * np.sin(np.arange(n) / SR * 2 * np.pi * 17))[:, None]
            x *= 2.4
        levels[stem] = float(np.sqrt((x ** 2).mean()))
        dry += gains[stem] * x
        wet += sends[stem] * gains[stem] * x
    lay, lay_wet = layers(s, tl, n, beat)
    mix = dry + lay + reverb(wet + lay_wet)
    mix -= mix.mean(axis=0)
    for sh in tl["shots"]:  # after the burst, a beat of near silence: everything, reverb too, falls away and returns
        if sh.get("burst"):
            i, j = int((sh["start_beat"] + sh["burst"] + 1) * beat * SR), int((sh["start_beat"] + sh["burst"] + 2) * beat * SR)
            duck = np.full(j - i, 0.045)
            edge = int(.05 * SR)
            duck[:edge] = np.linspace(1, 0.045, edge)
            mix[i:j] *= duck[:, None]
    fade = np.ones(n)
    tail = int(0.7 * SR)
    fade[-tail:] = np.linspace(1, 0, tail) ** 1.5
    mix *= fade[:, None]
    gain = 0.5 / max(1e-9, np.abs(mix).max())
    for _ in range(5):
        out = limit(mix * gain)
        write_wav(wav, out)
        i, lra, tp = loudness(wav)
        if abs(i - target) < 0.3:
            break
        gain *= 10 ** ((target - i) / 20)
    report(tl, wav, out, i, lra, tp, levels)
    read_score(s, tl, wav.replace("music.wav", "score.txt"))


def report(tl, wav, x, i, lra, tp, levels):
    print(f"music: {i:.1f} LUFS, range {lra:.1f} LU, true peak {tp:.1f} dBFS, clipped samples {(np.abs(x) >= 0.999).sum()}")
    print("  stem levels:", {k: round(20 * np.log10(max(v, 1e-9)), 1) for k, v in levels.items()})
    r = subprocess.run([FFMPEG, "-hide_banner", "-nostats", "-i", wav, "-af", "astats=metadata=0,silencedetect=noise=-50dB:d=0.3", "-f", "null", "-"], capture_output=True, text=True).stderr
    print("  peak (astats) " + " ".join(re.findall(r"Peak level dB: (-?[\d.]+)", r)[-1:]) + " dB; silences over 0.3 s: " + str(re.findall(r"silence_start: ([\d.]+)", r)))
    subprocess.run([FFMPEG, "-y", "-loglevel", "error", "-i", wav, "-lavfi", "showspectrumpic=s=1600x500:legend=1:scale=log", wav.replace(".wav", "-spectrum.png")], check=True)
    beat = 60 / tl["bpm"]
    w = int(0.06 * SR)
    rows = []
    for sh in tl["shots"]:
        at = int(sh["start_beat"] * beat * SR)
        if w <= at < len(x) - w:
            rows.append(f"{sh['id']}={np.sqrt((x[at:at + w] ** 2).mean() / max(1e-12, (x[at - w:at] ** 2).mean())):.1f}")
    print("  rise at each cut:", " ".join(rows))
    # Section loudness: the climax must be the loudest.
    secs = {}
    for sh in tl["shots"]:
        a, b = int(sh["start_beat"] * beat * SR), int((sh["start_beat"] + sh["beats"]) * beat * SR)
        secs.setdefault(sh["section"], []).append(x[a:b])
    print("  section level dB:", {k: round(float(10 * np.log10((np.concatenate(v) ** 2).mean())), 1) for k, v in secs.items()})
