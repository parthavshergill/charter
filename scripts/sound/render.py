#!/usr/bin/env python3
"""Makes every sound the game plays, and writes them to web/audio.

Nothing is downloaded. Short sounds come from simple physical recipes in numpy (a knock is a few decaying
tones, paper is shaped noise) and from single notes of the MuseScore General SoundFont, played by FluidSynth.
Each world's loop reuses the trailer's themes and instruments, from scripts/trailer/music.py.

A loop joins cleanly because of how it is made. Whatever rings past the end is added back at the start, and the
reverb wraps round too, so the audio is exactly periodic. The file holds a little more than one period at each
end. The player loops one period inside that, so a decoder that adds some silence at the start cannot move the join.

  python3 scripts/sound/render.py [--fx] [--music] [--only name,name] [--sf path/to/MuseScore_General.sf2]

The SoundFont is not in the repository. See web/audio/SOURCES.md. scripts/sound/check.py checks the results.
"""
import argparse, json, os, shutil, subprocess, sys, tempfile, wave
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, "scripts", "trailer"))
import music as M  # noqa: E402
from music import SR, Score, band, lowpass, decay, glide, resonate, write_midi  # noqa: E402

OUT = os.path.join(ROOT, "web", "audio")
FLUID = "/opt/homebrew/bin/fluidsynth"
FFMPEG = "/opt/homebrew/bin/ffmpeg"
DEFAULT_SF = os.path.expanduser("~/charter/results/trailer/soundfont/MuseScore_General.sf2")
OVERHANG = 0.25  # seconds of the loop repeated at each end of a music file. web/sound.js holds the same number.

rng = np.random.default_rng(1729)
HARP, VIBES, CELESTA, MARIMBA, GLOCK, TUBULAR, TRUMPET, TROMBONE, FLUTE, OBOE = 46, 11, 8, 12, 9, 14, 56, 57, 73, 68


# ---------------------------------------------------------------- the parts of a physical sound
def N(sec):
    return int(sec * SR)


def noise(n):
    return rng.uniform(-1, 1, n)


def end_soft(x, ms=12):
    """No sound stops dead: that is heard as a click."""
    k = min(N(ms / 1000), len(x))
    x = x.copy()
    x[-k:] *= np.linspace(1, 0, k) ** 1.5
    return x


def hit(f0, rate, dur=.25, ratios=(1, 2.2, 3.9, 5.4), amps=(1, .5, .28, .12), click=.3, click_rate=500):
    """Something solid struck: a few decaying tones and the short noise of the contact itself."""
    n = N(dur)
    t = np.arange(n) / SR
    x = np.zeros(n)
    for i, (r, a) in enumerate(zip(ratios, amps)):
        x += a * np.sin(2 * np.pi * f0 * r * (1 + rng.uniform(-.012, .012)) * t + rng.uniform(0, .6)) * np.exp(-t * rate * (1 + i * .35))
    x *= np.minimum(1, t / .0004)
    return end_soft(x + click * band(noise(n), 700, 9000) * np.exp(-t * click_rate))


def thump(f0, f1, dur, rate, shape=.6):
    """The table under it: a low tone that falls."""
    n = N(dur)
    return end_soft(glide(f0, f1, n / SR, shape)[:n] * decay(n, rate) * np.minimum(1, np.arange(n) / (.001 * SR)))


def layer(dur, *parts):
    """(when, sound, gain), mixed into one sound."""
    x = np.zeros(N(dur))
    for at, s, g in parts:
        k = N(at)
        s = s[: len(x) - k]
        x[k:k + len(s)] += g * s
    return x


def fade(x, ms=6):
    k = min(N(ms / 1000), len(x))
    x = x.copy()
    x[-k:] *= np.linspace(1, 0, k)
    return x


def room(x, seconds=.28, wet=.1):
    """A small room, so a sound sits on a table and not in the headphones."""
    n = N(seconds)
    t = np.arange(n) / SR
    ir = lowpass(noise(n), 5000) * np.exp(-t * 7 / seconds)
    ir /= np.sqrt((ir ** 2).sum())
    size = len(x) + n
    wetted = np.fft.irfft(np.fft.rfft(x, size) * np.fft.rfft(ir, size), size)
    y = wetted * wet
    y[: len(x)] += x
    return y


def paper(dur, lo=800, hi=7500, crackle=60):
    """Paper moving: shaped noise, with small crackles in it."""
    n = N(dur)
    env = np.sin(np.linspace(0, np.pi, n)) ** 1.5
    slow = np.interp(np.arange(n), np.linspace(0, n, 9), rng.uniform(.45, 1, 9))
    x = band(noise(n), lo, hi) * env * slow * .55
    bits = np.zeros(n)
    for _ in range(int(crackle * dur)):
        bits[rng.integers(0, n)] = rng.uniform(.3, 1) * rng.choice([-1, 1])
    return x + resonate(bits, [rng.uniform(2200, 3400), rng.uniform(4200, 6000)], 320) * env * .05


def coin(pitch=1.0, soft=True, rate=30):
    f = rng.uniform(.93, 1.07) * pitch
    x = hit(3100 * f, rate, .24, (1, 1.53, 2.21, 2.72), (1, .7, .46, .24), click=.18, click_rate=900)
    return lowpass(x, 9500) if soft else x


def scratch(dur):
    """A nib on paper: it sticks and slips, more than a hundred times a second."""
    n = N(dur)
    t = np.arange(n) / SR
    stick = (np.sin(2 * np.pi * rng.uniform(110, 170) * t + 2 * np.sin(2 * np.pi * rng.uniform(9, 17) * t)) > rng.uniform(-.3, .2)) * 1.0
    return band(noise(n), 2200, 8000) * lowpass(stick, 900) * np.sin(np.linspace(0, np.pi, n)) ** .7


# ---------------------------------------------------------------- notes from the SoundFont
class Font:
    """Plays a few notes through FluidSynth, dry, and gives back mono or stereo."""

    def __init__(self, path, folder):
        self.path, self.folder, self.count = path, folder, 0
        if not os.path.exists(path):
            raise SystemExit(f"No SoundFont at {path}. Pass --sf. web/audio/SOURCES.md says where it comes from.")

    def stereo(self, notes, dur, bpm=120, drums=()):
        """`notes` are (beat, program, midi note, beats, velocity). `drums` are (beat, key, velocity)."""
        s = Score(bpm)
        for b, prog, m, d, v in notes:
            s.note("x", prog, b, m, d, v)
        for b, key, v in drums:
            s.stems.setdefault("x", [])
            s.drum(b, key, v)
        ev = s.stems.get("x", []) + s.stems.get("drums", [])
        ev.append((round(dur * bpm / 60 * M.PPQ) + 8, 0, bytes([0xB0, 110, 0])))  # holds the file open for the note's tail
        self.count += 1
        mid, out = (os.path.join(self.folder, f"note{self.count}.{e}") for e in ("mid", "wav"))
        write_midi(mid, ev, bpm)
        subprocess.run([FLUID, "-ni", "-g", "0.6", "-r", str(SR), "-o", "synth.reverb.active=0", "-o", "synth.chorus.active=0", "-F", out, self.path, mid],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        with wave.open(out) as w:
            x = np.frombuffer(w.readframes(w.getnframes()), "<i2").reshape(-1, 2) / 32768
        os.remove(mid), os.remove(out)
        y = np.zeros((N(dur), 2))
        k = min(len(x), len(y))
        y[:k] = x[:k]
        tail = min(N(.08), len(y))
        y[-tail:] *= np.linspace(1, 0, tail)[:, None] ** 1.5
        return y

    def mono(self, notes, dur, bpm=120, drums=()):
        return self.stereo(notes, dur, bpm, drums).mean(axis=1)


# ---------------------------------------------------------------- the short sounds
def short_sounds(F):
    """Name to a list of takes. A take is mono, or stereo for the big moments."""

    def rattle():
        # Clacks that come fast, then spread out, inside the 360 ms the die tumbles.
        clacks = [(0.325 * (i / 9) ** .9 + rng.uniform(-.006, .006), hit(rng.uniform(1700, 2500), 190, .035, (1, 1.63, 2.4), (1, .55, .3), .5, 800), rng.uniform(.45, 1) * (1 - .4 * i / 9)) for i in range(1, 10)]
        tray = resonate(layer(.36, *clacks), [420, 910], 55) * .05
        return layer(.36, (0, hit(2000, 190, .035, (1, 1.63, 2.4), (1, .55, .3), .5, 800), .8), *clacks) + tray

    def land(heavy=0.0):
        f = rng.uniform(1350, 1650) * (1 - .25 * heavy)
        c = lambda g: hit(f * rng.uniform(.98, 1.04), 130, .06, (1, 1.63, 2.4), (1, .5, .28), .6, 700)
        return room(layer(.34, (0, c(1), 1), (.038, c(.5), .42), (.068, c(.2), .18), (0, thump(180 - 50 * heavy, 95 - 35 * heavy, .3, 26 - 12 * heavy), .3 + heavy * .8)), .2, .1)

    def spot():
        f = rng.uniform(560, 680)
        return room(layer(.3, (0, hit(f, 55, .2), 1), (.046, hit(f * 1.03, 75, .12), .3), (0, thump(190, 95, .2, 28), .42)), .24, .09)

    def link():
        f = rng.uniform(1200, 1450)
        slide = band(noise(N(.05)), 1500, 6000) * np.linspace(0, 1, N(.05)) ** 2 * .22
        return room(layer(.2, (0, slide, 1), (.05, hit(f, 95, .1, (1, 2.4, 4.3), (1, .45, .2)), .9), (.072, hit(f * 1.05, 120, .06, (1, 2.4), (1, .4)), .3), (.05, thump(240, 130, .1, 40), .28)), .2, .08)

    def upgrade():
        f = rng.uniform(410, 460)
        reward = F.mono([(0, MARIMBA, 74, .4, 62), (0, MARIMBA, 81, .4, 58)], .55)
        return room(layer(.62, (0, hit(f * 2.4, 110, .07), .5), (.06, hit(f, 38, .34), 1), (.06, thump(150, 70, .36, 18), .95), (.105, hit(f * 1.1, 80, .12), .24), (.06, reward, .9)), .26, .1)

    def refuse():
        muffle = lambda f: lowpass(hit(f, 70, .12, (1, 2.1), (1, .2), .12, 400), 1200)
        return room(layer(.26, (0, muffle(rng.uniform(205, 225)), 1), (.095, muffle(rng.uniform(170, 190)), .8)), .16, .05)

    def knock_knock():
        k = lambda g: hit(rng.uniform(320, 360), 60, .13, (1, 2.3), (1, .3), .18, 500) + thump(150, 110, .13, 32) * .5
        return room(layer(.3, (0, k(1), .8), (.112, k(1), 1)), .18, .07)

    def tap():
        return hit(rng.uniform(1650, 2050), 170, .05, (1, 2.4), (1, .3), .2, 900)

    def tool(f=1250):
        return room(layer(.11, (0, hit(f * rng.uniform(.98, 1.02), 95, .09, (1, 2.3, 4.1), (1, .4, .15), .22, 700), 1)), .12, .06)

    def run_of_coins(n=7, span=.42):
        return layer(span + .3, *[(span * (i / n) ** .8, coin(1 + .02 * i), rng.uniform(.5, 1) * (1 - .45 * i / n)) for i in range(n)])

    def payday():
        run = F.mono([(i * .11, HARP, m, .5, 66 + i * 3) for i, m in enumerate((74, 76, 78, 81, 83, 86))], 1.0)
        return room(layer(1.0, (0, run_of_coins(), .55), (.02, run, 1)), .3, .1)

    def your_turn():
        notes = [(0, VIBES, 81, .7, 104), (.34, VIBES, 86, 1.4, 112), (0, HARP, 69, .7, 92), (.34, HARP, 74, 1.4, 96), (.34, CELESTA, 86, 1.0, 70)]
        return room(F.mono(notes, 1.25), .4, .1)

    def bell():
        t = np.arange(N(.7)) / SR
        return sum(a * np.sin(2 * np.pi * f * t) * np.exp(-t * r) for f, a, r in ((2093, 1, 9), (4940, .34, 16), (6210, .18, 22))) * np.minimum(1, t / .0006)

    def offer_in():
        return room(layer(.82, (0, paper(.18), .45), (.13, bell(), .55), (.13, hit(1500, 200, .03, (1,), (1,), .3), .2)), .24, .1)

    def deal():
        rap = lambda: hit(rng.uniform(500, 540), 58, .14, (1, 2.3), (1, .35), .25, 500) + thump(170, 110, .14, 30) * .4
        tune = F.mono([(0, MARIMBA, 74, .5, 80), (0, MARIMBA, 81, .5, 76)], .55)
        return room(layer(.82, (0, rap(), .8), (.095, rap(), 1), (.2, tune, 1.1), (.2, coin(1.05), .24)), .26, .1)

    def bank():
        return room(layer(.52, *[(.03 + .042 * i ** 1.1, coin(1 - .03 * i, rate=38), .75 - .08 * i) for i in range(5)], (.25, hit(290, 55, .16, (1, 2.2), (1, .3), .25, 500), 1), (.25, thump(150, 90, .18, 24), .6)), .2, .08)

    def stamp(bright):
        n = N(.2)
        body = thump(190 if bright else 150, 80 if bright else 58, .2, 24) * .7
        slap = band(noise(n), 500 if bright else 300, 7000 if bright else 3000) * decay(n, 60)
        return room(body + .7 * slap + (hit(rng.uniform(860, 960), 120, .2, (1, 2.2), (1, .3), 0) * .35 if bright else 0), .18, .08)

    def seal():
        n = N(.8)
        low = F.mono([(0, M.TAIKO, 41, 1.2, 92)], .8)
        wax = band(noise(n), 200, 2600) * decay(n, 30) * .55
        return room(layer(.8, (0, thump(125, 44, .7, 9), .9), (0, wax, 1), (0, low, 1.2)), .35, .1)

    def law_fail():
        notes = [(0, M.TIMPANI, 38, .8, 66), (.02, M.PIZZ, 46, .6, 82), (.34, M.PIZZ, 45, .9, 66)]
        return room(lowpass(layer(.9, (0, F.mono(notes, .9), 1), (.02, paper(.2, 500, 2600, 30), .28)), 1500), .3, .06)

    def repeal():
        d = .42
        n = N(d)
        t = np.arange(n) / SR
        stick = lowpass((np.sin(2 * np.pi * np.cumsum(320 + 420 * t / d + 90 * np.sin(t * 61)) / SR) > 0) * 1.0, 2400)
        rip = band(noise(n), 1000, 9000) * stick * (np.linspace(.25, 1, n) ** 1.4) * np.minimum(1, (n - np.arange(n)) / (.01 * SR))
        return room(layer(.8, (0, rip, .8), (d, stamp(False), .8)), .24, .08)

    def monument():
        low = F.mono([(0, M.TAIKO, 38, 1.2, 84)], .9)
        n = N(.9)
        grit = band(noise(n), 300, 2400) * decay(n, 35) * .6
        return room(layer(.9, (0, thump(110, 45, .85, 9), 1), (0, grit, 1), (0, low, .9), (.09, hit(300, 80, .12, (1, 2.1), (1, .3), .4), .25)), .4, .1)

    def law_fire():
        ting = hit(1568, 14, .4, (1, 2.1), (1, .3), 0)
        return room(layer(.46, (0, stamp(True), .7), (.01, ting, .13)), .2, .08)

    def gavel():
        g = lambda: hit(rng.uniform(620, 660), 45, .16, (1, 2.3, 4.0), (1, .4, .15), .3, 600) + thump(190, 120, .16, 26) * .5
        return room(layer(.5, (0, g(), .8), (.17, g(), 1)), .24, .1)

    def draft_ready():
        return room(F.mono([(0, HARP, 74, .8, 82), (.24, HARP, 81, 1.2, 86)], .95), .3, .08)

    def crash():
        L, R = M.impact()[: N(1.9)], M.impact()[: N(1.9)]
        glass = lambda: layer(1.0, *[(rng.uniform(0, .62), np.sin(2 * np.pi * rng.uniform(2600, 9000) * np.arange(N(.1)) / SR) * decay(N(.1), rng.uniform(30, 60)), rng.uniform(.15, .55)) for _ in range(46)])
        out = np.stack([L * .85, R * .85], axis=1)
        out[: N(1.0), 0] += glass()
        out[: N(1.0), 1] += glass()
        k = N(.5)
        out[-k:] *= (np.linspace(1, 0, k) ** 1.5)[:, None]
        return out

    def fall():
        f = rng.uniform(460, 620)
        n = N(.6)
        dust = lowpass(noise(n), 1500) * np.exp(-np.arange(n) / SR * 11) * .1
        bounces = [(0, 1), (.09, .62), (.16, .42), (.21, .28), (.245, .18), (.27, .12)]
        return room(layer(.6, *[(at, hit(f * rng.uniform(.95, 1.1), 70, .1, (1, 2.3, 3.7), (1, .45, .2), .3, 500), g) for at, g in bounces], (0, dust, 1), (0, thump(160, 90, .18, 26), .5)), .24, .09)

    def rumble():
        x = M.fx_rumble()[: N(1.45)]
        k = N(.4)
        x[-k:] *= np.linspace(1, 0, k) ** 1.5
        return x

    def rare():
        d = .26
        n = N(d)
        t = np.arange(n) / SR
        whoosh = end_soft(band(noise(n), 500, 5200) * (t / d) ** 2, 30)
        notes = [(.48, TUBULAR, 81, 1.6, 86), (.48, GLOCK, 86, 1.0, 88), (.6, GLOCK, 90, 1.0, 88), (.72, GLOCK, 93, 1.4, 96), (.48, HARP, 74, 1.4, 80)]
        return room(layer(1.45, (0, whoosh, .32), (0, F.mono(notes, 1.45), 1.0), (.24, thump(170, 90, .2, 22), .4)), .45, .12)

    def lead():
        notes = [(0, M.HORN, 57, .4, 88), (0, HARP, 69, .4, 78), (.36, M.HORN, 62, 1.5, 100), (.36, M.HORN, 69, 1.5, 84), (.36, HARP, 74, 1.5, 84), (.36, GLOCK, 86, .8, 52), (.36, M.TIMPANI, 38, .7, 70)]
        return room(F.mono(notes, 1.3), .4, .1)

    def lead_lost():
        return room(lowpass(F.mono([(0, M.HORN, 62, .4, 58), (.36, M.HORN, 57, 1.1, 50)], .95), 1800), .35, .08)

    def score_up(top):
        return room(F.mono([(0, MARIMBA, top - 5, .2, 74), (.09, MARIMBA, top, .6, 92)], .48), .2, .08)

    def score_down():
        return room(lowpass(F.mono([(0, MARIMBA, 69, .2, 66), (.11, MARIMBA, 65, .6, 62)], .48), 2600), .2, .05)

    def win():
        tune = [(0, 69, .34), (.34, 69, .34), (.68, 74, .66), (1.34, 69, .33), (1.67, 74, .33), (2, 78, .66), (2.66, 81, .67), (3.33, 86, 2.5)]
        notes = [(b, TRUMPET, m, d, 104) for b, m, d in tune] + [(b, TRUMPET, m - 12, d, 86) for b, m, d in tune]
        for b, ms, d in ((0, (50, 57, 62), 2), (2, (50, 57, 66), 1.33), (3.33, (50, 57, 62, 66, 69), 2.5)):
            notes += [(b, M.HORN, m, d, 82) for m in ms] + [(b, M.STRINGS, m + 12, d, 78) for m in ms]
        notes += [(b, M.TUBA, 38, d, 84) for b, d in ((0, 1.9), (2, 1.2), (3.33, 2.4))]
        notes += [(b, M.TIMPANI, 38, .9, v) for b, v in ((0, 104), (.68, 82), (2, 96), (3.33, 118))]
        notes += [(2.66 + i * .11, HARP, m, 2.4, 78) for i, m in enumerate((62, 66, 69, 74, 78, 81))]
        return stereo_room(F.stereo(notes, 3.9), .9, .14)

    def lose():
        notes = [(0, M.STRINGS, m, 2.9, 58) for m in (50, 57, 62, 65)] + [(0, M.BASS, 38, 2.9, 60)]
        notes += [(0, M.HORN, 69, .95, 66), (1, M.HORN, 65, .95, 62), (2, M.HORN, 62, 1.8, 60), (2, M.TIMPANI, 38, 1, 54)]
        return stereo_room(F.stereo(notes, 2.3, bpm=90), .9, .14)

    def end_of_game():
        notes = [(i * .17, HARP, m, 2.2, 84) for i, m in enumerate((50, 57, 62, 66, 69, 74))] + [(0, M.STRINGS, m, 2.6, 58) for m in (50, 57, 62, 66)]
        return stereo_room(F.stereo(notes, 2.3), .7, .12)

    def begin():
        notes = [(0, M.TIMPANI, 38, .6, 78), (.5, M.TIMPANI, 38, .6, 70), (1, M.TIMPANI, 38, 1, 92), (1, M.HORN, 57, .5, 78), (1.5, M.HORN, 62, 1.3, 90), (1.5, M.HORN, 69, 1.3, 74), (1.5, HARP, 74, 1.3, 70)]
        return stereo_room(F.stereo(notes, 1.75), .7, .1)

    return {
        "tool": [tool(1250), tool(1320)], "tool-off": [tool(900)], "tap": [tap(), tap(), tap()],
        "place-spot": [spot(), spot(), spot()], "place-link": [link(), link(), link()], "place-up": [upgrade(), upgrade()],
        "refuse": [refuse(), refuse()], "end-turn": [knock_knock(), knock_knock()],
        "page": [room(paper(rng.uniform(.17, .27)), .14, .05) for _ in range(4)],
        "dice-rattle": [rattle(), rattle(), rattle()], "dice-land": [land(), land(), land()], "dice-hard": [land(1), land(1)],
        "coin": [coin() for _ in range(5)], "card-out": [paper(rng.uniform(.07, .1), 1200, 7000, 30) for _ in range(3)], "payday": [payday(), payday()],
        "your-turn": [your_turn()],
        "offer-in": [offer_in()], "deal": [deal()], "bank": [bank(), bank()],
        "quill": [scratch(rng.uniform(.05, .09)) for _ in range(4)],
        "stamp-yes": [stamp(True) for _ in range(3)], "stamp-no": [stamp(False) for _ in range(3)],
        "seal": [seal(), seal()], "law-fail": [law_fail()], "repeal": [repeal()], "monument": [monument()], "law-fire": [law_fire(), law_fire()],
        "vote-call": [gavel()], "draft-ready": [draft_ready()],
        "crash": [crash()], "fall": [fall(), fall()], "rumble": [rumble()], "rare": [rare()], "lead": [lead()], "lead-lost": [lead_lost()],
        "score-up": [score_up(86), score_up(81)], "score-down": [score_down()],
        "win": [win()], "lose": [lose()], "end": [end_of_game()], "begin": [begin()],
        "talk": [hit(rng.uniform(2200, 2600), 220, .03, (1, 2.1), (1, .25), .3, 1200) for _ in range(2)],
    }


def stereo_room(x, seconds, wet):
    y = [room(x[:, c], seconds, wet) for c in range(2)]
    k = N(.08)
    out = np.stack(y, axis=1)
    out[-k:] *= np.linspace(1, 0, k)[:, None]
    return out


def encode(x, path, stereo=False, rate="64k"):
    """A WAV goes in and a small MP3 comes out. MP3 is the one format every browser decodes without help."""
    wav = path + ".wav"
    channels = 2 if stereo else 1
    with wave.open(wav, "wb") as w:
        w.setnchannels(channels)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes((np.clip(x, -1, 1) * 32767).astype("<i2").tobytes())
    subprocess.run([FFMPEG, "-y", "-loglevel", "error", "-i", wav, "-map_metadata", "-1", "-c:a", "libmp3lame", "-b:a", rate, path], check=True)
    os.remove(wav)


def write_fx(F, only):
    global rng
    rng = np.random.default_rng(1729)
    folder = os.path.join(OUT, "fx")
    os.makedirs(folder, exist_ok=True)
    takes_of = {}
    for name, takes in short_sounds(F).items():
        takes_of[name] = len(takes)
        if only and name not in only:
            continue
        for i, x in enumerate(takes):
            x = x - x.mean(axis=0)
            x = x / max(1e-9, np.abs(x).max()) * .708  # 3 dB under full scale. web/sound.js sets how loud each one plays.
            x = fade(x) if x.ndim == 1 else x
            stereo = x.ndim == 2
            encode(x, os.path.join(folder, f"{name}-{i + 1}.mp3"), stereo, "112k" if stereo else "64k")
        print(f"{name}: {len(takes)}")
    return takes_of


# ---------------------------------------------------------------- the loops
def tune(line, shift=0):
    return [(o, m + shift, d) for o, m, d in line]


F_CH, C_CH, BB_CH, DM_CH, G_CH, A_CH = [53, 60, 65], [55, 60, 64], [53, 58, 62], [50, 57, 62], [50, 55, 62], [52, 57, 61]


def gut(s, a, beats, chord, v=50, prog=M.GUITAR):
    """The trailer's plucked gut string, in eighths over a chord."""
    low, mid, high = chord[0] + 12, chord[1] + 12, chord[2] + 12
    for i in range(beats * 2):
        s.note("pluck", prog, a + i / 2, [low, mid, high, mid][i % 4], .9, v + (8 if i % 4 == 0 else 0), loose=.01, part="gut string")


def table(s, n):
    """Tutorial Island, and any world with no track of its own: the game's own theme in F, as in the trailer's opening."""
    bars = [(F_CH, 4), (C_CH, 4), (F_CH, 4), (C_CH, 4), (BB_CH, 4), (C_CH, 4), (F_CH, 4), (C_CH, 4)]
    a = 0
    while a < n:
        section = a // 32
        b = a
        for chord, d in bars:
            gut(s, b, d, chord, 40 if section % 4 == 0 else 46)
            M.pad(s, b, d, chord, 34 if section % 4 == 0 else 42, swell=(58, 86))
            s.note("strings", M.BASS, b, chord[0] - 12, d, 44, part="bass")
            b += d
        if section % 4 == 1:
            M.violin_line(s, a, M.THEME_TURN, 74, double=38)
            M.violin_line(s, a + 16, tune(M.THEME_TURN, -12), 66, prog=M.CELLO, stem="strings", part="cello")
            M.frame_drum(s, a + 16, 4, 38)
        elif section % 4 == 2:
            M.violin_line(s, a, tune([x for x in M.THEME_HIGH if x[0] < 16], -12), 70, double=40)
            M.frame_drum(s, a, 8, 42)
            for off, m, d in M.THEME_TURN:
                s.note("winds", M.HORN, a + 16 + off, m - 12, d, 54, part="horn")
        elif section % 4 == 3:
            for off, m, d in M.THEME_TURN:
                s.note("winds", FLUTE, a + off, m + 12, d, 52, part="flute")
            M.frame_drum(s, a + 16, 4, 36)
        a += 32


def not_catan(s, n):
    """Not Catan: the same tune turned to D Dorian, slower and plainer, with a squeezebox for a drone."""
    plan = [(DM_CH, 4), (G_CH, 4), (DM_CH, 4), (BB_CH, 2), (C_CH, 2)]
    a = 0
    while a < n:
        section = a // 16
        b = a
        for chord, d in plan:
            gut(s, b, d, chord, 42, M.GUITAR)
            for m in chord:
                s.note("winds", M.ACCORDION, b, m + 12, d, 36, loose=.01, part="drone")
            s.note("strings", M.BASS, b, chord[0] - 12, d, 46, part="bass")
            b += d
        if section % 3 == 1:
            M.violin_line(s, a, tune(M.THEME_TURN, -3), 72, stem="solo")
        elif section % 3 == 2:
            for i in range(32):
                s.note("winds", M.BASSOON, a + i / 2, M.HORNPIPE[i % len(M.HORNPIPE)] - 12, .44, 56 if i % 2 == 0 else 46, loose=.01, part="hornpipe")
        if section % 2 == 1:
            M.frame_drum(s, a, 4, 34)
        a += 16


def slime(s, n):
    """Slime Parliament: the melody gone wet. Pizzicato that sags, a tuba under it, and the bubbling in `slime_layer`."""
    a = 0
    while a < n:
        section = a // 12
        if section % 3 != 2:
            for off, m, d in M.THEME_SLIME:
                b = a + off
                up = 12 if section % 6 == 4 else 0
                s.note("pluck", M.PIZZ, b, m + up, min(d, .8), 82, part="melody")
                s.droop("pluck", M.PIZZ, b, min(d, .8))
                s.note("winds", M.BASSOON, b, m - 12, min(d, .45) * .8, 50, part="bassoon")
        else:
            for i in range(0, 12, 2):
                s.note("winds", M.BASSOON, a + i, [50, 53, 57, 53, 48, 50][i // 2], 1.4, 46, part="bassoon")
        for i in range(12):
            s.note("winds", M.TUBA, a + i, (38 if i % 4 < 2 else 45) if i < 8 else (36 if i < 10 else 38), .42, 62 if i % 2 == 0 else 42, part="tuba")
        M.pad(s, a, 12, [50, 57, 62], 30, swell=(50, 74))
        a += 12


def slime_layer(x, beat, n):
    y = np.zeros(n)
    for _ in range(int(n / SR * 3.2)):
        place(y, M.bubble_pop(), rng.integers(0, n), .05)
    for i in range(0, int(n / SR / beat), 6):
        place(y, M.squelch(), int((i + 3.5) * beat * SR), .05)
    x += np.stack([y, y], axis=1)


def bubble(s, n):
    """The AI Bubble: glass strings that climb a half step at a time, then fall back. It never quite bursts."""
    climb = [0, 1, 2, 1]
    for k in range(n // 16):
        a, up = k * 16, climb[k % 4]
        for m in (74, 77, 81):
            s.note("glass", M.TREMOLO, a, m + up, 16, 38 + 6 * up, part="glass")
        s.cc("glass", M.TREMOLO, 11, a, a + 16, 62 + 8 * up, 96 + 8 * up)
        s.note("strings", M.BASS, a, 38 + up, 16, 42, part="bass")
        s.note("strings", M.CELLO, a, 50 + up, 16, 38, part="drone")
        if k % 4 in (1, 2):
            for off, m, d in ((0, 86, 2), (2, 89, 2), (4, 90, 2), (6, 91, 2), (8, 89, 4), (12, 86, 4)):
                s.note("glass", M.VIOLIN, a + off, m + up, d, 50, part="glass melody")


def bubble_layer(x, beat, n):
    y = np.zeros(n)
    beats = int(round(n / SR / beat))
    for i in range(beats * 2):
        up = [0, 1, 2, 1][(i // 32) % 4]
        cut = 500 + 1500 * ((i % 32) / 32) ** 1.5 + 280 * up
        place(y, M.cold_pulse(38 + up + (12 if i % 8 == 6 else 0), .22, cut), int(i / 2 * beat * SR), .12 + .02 * up)
    x += np.stack([y, y], axis=1)


def pirate(s, n):
    """The Pirate Republic: the trailer's hornpipe, slower and quieter, passed between fiddle and squeezebox."""
    a = 0
    while a < n:
        section = a // 24
        for k in range(a, a + 24, 12):
            for i in range(12):
                j = i % 12
                root, chord = ((38, [62, 65, 69]) if j < 4 or 6 <= j < 10 else (43, [62, 67, 71]) if j < 6 else (36, [60, 64, 67]))
                t = k + i
                s.note("winds", M.TUBA, t, root if i % 2 == 0 else root + 7, .4, 50, part="bass")
                for m in chord:
                    s.note("winds", M.ACCORDION, t + .5, m, .34, 42, part="squeezebox")
                s.drum(t, 36 if i % 2 == 0 else 39, 58 if i % 2 == 0 else 34, "stomp and clap")
        for i in range(48):
            m = M.HORNPIPE[i % len(M.HORNPIPE)]
            swing = .08 if i % 2 else 0.0
            if section % 3 == 0:
                s.note("solo", M.FIDDLE, a + i / 2 + swing, m, .46, 70 if i % 2 == 0 else 56, part="hornpipe")
            elif section % 3 == 1:
                s.note("winds", M.ACCORDION, a + i / 2 + swing, m - 12, .46, 58 if i % 2 == 0 else 46, part="hornpipe")
            elif i % 2 == 0:
                s.note("pluck", M.GUITAR, a + i / 2, m - 12, .8, 52, part="hornpipe")
        a += 24


def pirate_layer(x, beat, n):
    y = np.zeros(n)
    for i in range(0, int(n / SR / beat), 16):
        place(y, M.creak(), int((i + 7.75) * beat * SR), .07)
    x += np.stack([y, y], axis=1)


def strike(s, n):
    """Strike the Earth: low horns and basses under the rising fourth, as dwarves would play it. The anvil is in `strike_layer`."""
    a = 0
    while a < n:
        section = a // 16
        root = 38 if section % 4 != 2 else 34
        for i in range(16):
            r = root if i < 8 else (34 if root == 38 else 36)
            s.note("winds", M.TUBA, a + i, r, .8, 58 if i % 2 == 0 else 42, part="bass")
            if i % 4 == 0:
                s.note("strings", M.BASS, a + i, r, 3.8, 46, part="bass")
                s.note("strings", M.CELLO, a + i, r + 19 if r + 19 <= 76 else r + 7, 3.8, 36, part="fifth")
        if section % 2 == 1:
            for off, m, d in ((0, 57, 2), (2, 62, 2), (4, 64, 2), (6, 65, 6), (12, 64, 2), (14, 62, 2)):
                s.note("winds", M.HORN, a + off, m, d, 62, part="melody")
                s.note("winds", M.HORN, a + off, max(41, m - 7), d, 48, part="horn fifth")
        elif section % 4 == 2:
            for off, m, d in ((0, 50, 4), (4, 53, 4), (8, 55, 4), (12, 53, 4)):
                s.note("winds", M.BASSOON, a + off, m, d, 50, part="bassoon")
        for i in range(0, 16, 4):
            s.note("perc", M.TAIKO, a + i, 41, 1.2, 50, part="taiko")
            s.note("perc", M.TAIKO, a + i + 2.5, 41, .8, 32, part="taiko")
        a += 16


def strike_layer(x, beat, n):
    y = np.zeros(n)
    for i in range(0, int(n / SR / beat), 8):
        place(y, M.fx_anvil(), int((i + 2) * beat * SR), .05)
        if i % 16 == 8:
            place(y, M.fx_anvil(), int((i + 3) * beat * SR), .035)
    x += np.stack([y, y], axis=1)


def place(y, x, at, g):
    """Puts a sound in a loop. What runs off the end comes in at the start."""
    idx = (at + np.arange(len(x))) % len(y)
    np.add.at(y, idx, g * x)


# name: (arrangement, tempo, beats, what numpy adds, seed). About a minute and a half each.
TRACKS = {
    "table": (table, 88, 128, None, 11),
    "not-catan": (not_catan, 80, 112, None, 12),
    "slime": (slime, 84, 120, slime_layer, 13),
    "bubble": (bubble, 104, 160, bubble_layer, 14),
    "pirate": (pirate, 112, 168, pirate_layer, 15),
    "strike": (strike, 72, 112, strike_layer, 16),
}
STEM_GAIN = {"solo": 1.5, "strings": .85, "pluck": 1.15, "winds": .9, "perc": .8, "drums": 1.2, "glass": 1.1}
STEM_SEND = {"solo": .5, "strings": .5, "pluck": .3, "winds": .45, "perc": .35, "drums": .2, "glass": .7}


def circular_reverb(wet, seconds=2.2):
    n, k = len(wet), int(seconds * SR)
    t = np.arange(k) / SR
    out = np.zeros_like(wet)
    for c in range(2):
        ir = np.convolve(rng.uniform(-1, 1, k), np.ones(8) / 8, "same") * np.exp(-t * 3.2)
        ir[: int(.018 * SR)] = 0
        out[:, c] = np.fft.irfft(np.fft.rfft(wet[:, c]) * np.fft.rfft(ir, n), n)
    return out * .12


def render_track(name, sf, folder):
    global rng
    lay, bpm, beats, numpy_layer, seed = TRACKS[name]
    M.rng, rng = np.random.default_rng(seed), np.random.default_rng(seed + 100)  # each track comes out the same every time
    beat = 60 / bpm
    n = int(round(beats * beat * SR))
    tail = int(4 * SR)
    s = Score(bpm)
    lay(s, beats)
    dry, wet = np.zeros((n, 2)), np.zeros((n, 2))
    stems = os.path.join(folder, name)
    for stem, ev in s.stems.items():
        ev.append((round((beats + 4 / beat) * M.PPQ), 0, bytes([0xB0, 110, 0])))  # holds the file open past the end, for the last notes' tails
        x = M.render_stem(ev, bpm, sf, stems, stem, n + tail)
        x[:tail] += x[n:n + tail]  # what rang past the end comes in at the start
        x = x[:n]
        if stem == "glass":
            # The trailer's glass: strings thinned to their edge, and shaken. The shake goes a whole number of times round the loop.
            for c in range(2):
                x[:, c] = M.band(x[:, c], 1400, 11000)
            shake = round(17 * n / SR) / (n / SR)
            x = x * (0.72 + 0.28 * np.sin(np.arange(n) / SR * 2 * np.pi * shake))[:, None] * 2.4
        dry += STEM_GAIN[stem] * x
        wet += STEM_SEND[stem] * STEM_GAIN[stem] * x
    if numpy_layer:
        numpy_layer(dry, beat, n)
    mix = dry + circular_reverb(wet)
    mix -= mix.mean(axis=0)
    shutil.rmtree(stems, ignore_errors=True)
    return mix, n / SR


def write_music(sf, folder, only):
    out = os.path.join(OUT, "music")
    os.makedirs(out, exist_ok=True)
    table_path = os.path.join(out, "tracks.json")
    lengths = json.load(open(table_path)) if os.path.exists(table_path) else {}
    for name in TRACKS:
        if only and name not in only:
            continue
        mix, seconds = render_track(name, sf, folder)
        # One gain for the whole loop, and a soft top: neither has a memory, so the loop stays periodic.
        probe = os.path.join(folder, "probe.wav")
        gain = .25 / max(1e-9, np.abs(mix).max())
        for _ in range(4):
            M.write_wav(probe, np.tanh(mix * gain * 1.0))
            i = M.loudness(probe)[0]
            if abs(i + 20) < .3:
                break
            gain *= 10 ** ((-20 - i) / 20)
        final = np.tanh(mix * gain)
        k = int(OVERHANG * SR)
        whole = np.concatenate([final[-k:], final, final[:k]])
        wav = os.path.join(folder, f"{name}.wav")
        M.write_wav(wav, whole)
        path = os.path.join(out, f"{name}.mp3")
        subprocess.run([FFMPEG, "-y", "-loglevel", "error", "-i", wav, "-map_metadata", "-1", "-c:a", "libmp3lame", "-b:a", "80k", "-joint_stereo", "1", path], check=True)
        os.remove(wav)
        lengths[name] = seconds
        print(f"{name}: {seconds:.2f} s, {os.path.getsize(path) // 1024} KB, peak {20 * np.log10(np.abs(final).max()):.1f} dBFS")
    with open(table_path, "w") as f:
        json.dump({k: lengths[k] for k in sorted(lengths)}, f, indent=0)
        f.write("\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fx", action="store_true")
    ap.add_argument("--music", action="store_true")
    ap.add_argument("--only", default="")
    ap.add_argument("--sf", default=os.environ.get("CHARTER_SOUNDFONT", DEFAULT_SF))
    a = ap.parse_args()
    only = set(filter(None, a.only.split(",")))
    both = not a.fx and not a.music
    temp = tempfile.mkdtemp(prefix="charter-sound-")
    try:
        if a.fx or both:
            write_fx(Font(a.sf, temp), only)
        if a.music or both:
            if not os.path.exists(a.sf):
                raise SystemExit(f"No SoundFont at {a.sf}. Pass --sf.")
            write_music(a.sf, temp, only)
    finally:
        shutil.rmtree(temp, ignore_errors=True)


if __name__ == "__main__":
    main()
