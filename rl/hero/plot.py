"""The hero plot: how often the trained policy wins, across one training run's checkpoints.

    python3 rl/hero/plot.py            # reads rl/hero/data/*.csv, writes rl/hero/hero{,-dark}.png and hero.svg

Data:
- data/eval.csv (collect.py): rl/eval tables, one row per checkpoint, game and opponent.
- data/sonnet.csv (optional): games against three Sonnet seats: arm, steps, games, wins, target_wins.
- data/can_play.txt: eval's "can it play" line for each checkpoint.
"""
import csv
import math
import os
import re

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
MAIN_RUN = "hero-v2"          # imitation warm start, then PPO; waiting-row fix; champion bots in 50% of games
BEST_RUN, BEST_STEPS = "v2-long-champ", 39321600   # Candidate 4: a separate lineage, drawn as one labelled point
BEST_TOTAL = 59965440 + 39321600                     # its total PPO steps: 60M in v2-stale, then 39.3M
REF_RUN = "ref"               # rl/eval with `hand` itself as the subject, the same seeds
SCRATCH_RUN = "v2-mix"        # the same network, PPO from random weights, hand bots in 25% of games
TRAIN = ["island", "not-catan"]
HELD_OUT = ["slime-parliament", "ai-bubble", "strike-the-earth", "pirate-republic"]
WORLD = {"slime-parliament": "Slime Parliament", "ai-bubble": "AI Bubble", "strike-the-earth": "Strike the Earth",
         "pirate-republic": "Pirate Republic"}
ROUNDS = {"slime-parliament": 24, "ai-bubble": 10, "strike-the-earth": 10, "pirate-republic": 10}

THEMES = {
    "light": {"bg": "#fcfcfb", "ink": "#0b0b0b", "ink2": "#52514e", "muted": "#8a8984", "grid": "#e4e3df",
              "random": "#1baf7a", "hand": "#2a78d6", "champion-closed": "#eb6834", "sonnet": "#6250d6"},
    "dark": {"bg": "#1a1a19", "ink": "#f0efec", "ink2": "#c3c2b7", "muted": "#8f8e86", "grid": "#33332f",
             "random": "#199e70", "hand": "#3987e5", "champion-closed": "#d95926", "sonnet": "#9085e9"},
}
LABEL = {"random": "vs 3 random players", "hand": "vs 3 rule-based bots",
         "champion-closed": "vs 3 evolved rivals*"}


def wilson(w, n, z=1.96):
    if n == 0:
        return 0.0, 0.0
    p = w / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def load_eval():
    rows = list(csv.DictReader(open(os.path.join(HERE, "data", "eval.csv"))))
    for r in rows:
        for k in ("steps", "games", "wins", "target_wins", "limit_wins"):
            r[k] = int(r[k])
    return rows


def series(rows, run, opponent, games):
    """(steps, win rate, low, high, wins, n) per checkpoint, summed over `games`."""
    by = {}
    for r in rows:
        if r["run"] == run and r["opponent"] == opponent and r["game"] in games:
            w, n = by.get(r["steps"], (0, 0))
            by[r["steps"]] = (w + r["wins"], n + r["games"])
    out = []
    for s in sorted(by):
        w, n = by[s]
        lo, hi = wilson(w, n)
        out.append((s, w / n, lo, hi, w, n))
    return out


def load_sonnet():
    path = os.path.join(HERE, "data", "sonnet.csv")
    if not os.path.exists(path):
        return []
    return [dict(r, steps=int(r["steps"]), games=int(r["games"]), wins=int(r["wins"]))
            for r in csv.DictReader(open(path)) if int(r["games"]) > 0]


def can_play_line(run, steps):
    """Eval's can-it-play result for one checkpoint: (PASS or FAIL, games, ended, refused), or None."""
    path = os.path.join(HERE, "data", "can_play.txt")
    if not os.path.exists(path):
        return None
    for line in open(path):
        m = re.match(r"(\S+) (\d+) (PASS|FAIL): (\d+) games, (\d+) ended, (\d+) refused", line)
        if m and m.group(1) == run and int(m.group(2)) == steps:
            return m.group(3, 4, 5, 6)
    return None


SONNET_ROWS = [  # (weights label in data/sonnet.csv steps, row label)
    (0, "imitation start"),
    (29491200, "v2-fix, 29.5M"),
    (44236800, "v2-fix, 44.2M"),
    (BEST_TOTAL, "best (Candidate 4)"),
]


def style(a, t):
    a.set_facecolor(t["bg"])
    for side in ("top", "right"):
        a.spines[side].set_visible(False)
    a.tick_params(length=0)


def draw(theme_name, rows, sonnet, out_paths):
    t = THEMES[theme_name]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 15, "text.color": t["ink"],
                         "axes.labelcolor": t["ink2"], "xtick.color": t["ink2"], "ytick.color": t["ink2"],
                         "axes.edgecolor": t["grid"], "svg.fonttype": "none"})
    fig = plt.figure(figsize=(16, 9), facecolor=t["bg"])
    ax = fig.add_axes([0.065, 0.20, 0.45, 0.60])     # main chart
    bx = fig.add_axes([0.815, 0.53, 0.165, 0.27])     # held-out worlds
    sx = fig.add_axes([0.815, 0.20, 0.165, 0.22])     # Sonnet
    for a in (ax, bx, sx):
        style(a, t)
    M = 1e6
    main = {o: series(rows, MAIN_RUN, o, TRAIN) for o in ("random", "hand", "champion-closed")}
    xmax = BEST_TOTAL / M + 3

    # references: an equal player, and our rule-based bot's own score on the same seeds
    ax.axhline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)), zorder=1)
    ref = series(rows, REF_RUN, "hand", TRAIN)
    if ref:
        _, rp, rlo, rhi, _, _ = ref[0]
        ax.axhspan(100 * rlo, 100 * rhi, color=t["ink2"], alpha=0.09, lw=0, zorder=1)

    # from-scratch PPO, same network, a separate run: grey dotted lines
    scratch = {o: series(rows, SCRATCH_RUN, o, TRAIN) for o in ("random", "hand")}
    for o, s in scratch.items():
        if s:
            ax.plot([q[0] / M for q in s], [100 * q[1] for q in s], color=t["muted"], lw=2, ls=(0, (1, 2.2)),
                    zorder=2, dash_capstyle="round")
    if scratch["random"] and scratch["hand"]:
        r, h = scratch["random"][-1], scratch["hand"][-1]
        ax.annotate(f"dotted: the same network, PPO from scratch (a separate run):\n"
                    f"{100 * r[1]:.0f}% vs random players, {100 * h[1]:.0f}% vs rule-based bots",
                    xy=(30, 100 * scratch["random"][2][1] + 0.8), xytext=(22, 52), color=t["ink2"], fontsize=12.5,
                    arrowprops=dict(arrowstyle="-", color=t["muted"], lw=1))

    # the main run
    labels = []
    for o, s in main.items():
        if not s:
            continue
        xs = [q[0] / M for q in s]
        ax.fill_between(xs, [100 * q[2] for q in s], [100 * q[3] for q in s], color=t[o], alpha=0.18, lw=0, zorder=2)
        ax.plot(xs, [100 * q[1] for q in s], color=t[o], lw=2.6, zorder=3, solid_capstyle="round")
        ax.plot(xs, [100 * q[1] for q in s], "o", color=t[o], ms=6, mec=t["bg"], mew=1.5, zorder=4)
        y = 100 * s[-1][1]
        labels.append((y, f"{y:.0f}%  {LABEL[o]}", t["ink"], "bold" if o == "hand" else "normal", t[o]))

    # Candidate 4: the best checkpoint of another lineage, one point at its total PPO steps
    c4 = [q for q in series(rows, BEST_RUN, "hand", TRAIN) if q[0] == BEST_STEPS]
    if c4:
        _, cp_, clo, chi, _, _ = c4[0]
        x = BEST_TOTAL / M
        ax.plot([x, x], [100 * clo, 100 * chi], color=t["hand"], lw=2, zorder=5)
        ax.plot([x], [100 * cp_], "s", ms=10, color=t["bg"], mec=t["hand"], mew=2.4, zorder=6)
        labels.append((100 * cp_, f"{100 * cp_:.0f}%  best checkpoint, another run", t["ink2"], "normal", t["hand"]))
    labels.append((25, "25%  an equal player", t["ink2"], "normal", t["ink2"]))
    if ref:
        labels.append((100 * rp, f"{100 * rp:.0f}%  our rule-based bot itself", t["ink2"], "normal", t["ink2"]))

    # direct labels in a column right of the chart, kept 4.5 points apart
    placed = []
    for y, text, color, weight, mark in sorted(labels, key=lambda l: -l[0]):
        ly = min([y] + [q - 4.5 for q in placed])
        placed.append(ly)
        ax.annotate(text, xy=(xmax, y), xytext=(xmax + 3, ly), color=color, fontsize=13, fontweight=weight,
                    va="center", ha="left", annotation_clip=False,
                    arrowprops=dict(arrowstyle="-", color=mark, lw=1, shrinkA=0, shrinkB=0))

    ax.annotate("start: imitation of\nour rule-based bot", xy=(0, 100 * main["hand"][0][1]) if main["hand"] else (0, 10),
                xytext=(2, 38), color=t["ink2"], fontsize=12, arrowprops=dict(arrowstyle="-", color=t["muted"], lw=1))
    ax.set_xlim(-2, xmax)
    ax.set_ylim(0, 102)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_yticklabels(["0%", "25%", "50%", "75%", "100%"])
    ax.set_xlabel("PPO training steps (millions)")
    ax.set_ylabel("win rate, 1 bot vs 3 opponents")
    ax.grid(axis="y", color=t["grid"], lw=1)
    ax.set_axisbelow(True)
    ax.set_title("Training worlds (Island, Not Catan)", loc="left", fontsize=15, color=t["ink2"], pad=10)

    # held-out worlds, best checkpoint of the main run, vs our rule-based bots: real wins solid, round-limit faded
    best = main["hand"][-1][0] if main["hand"] else None
    for i, g in enumerate(HELD_OUT):
        sel = [r for r in rows if r["run"] == MAIN_RUN and r["steps"] == best and r["game"] == g
               and r["opponent"] == "hand"]
        if not sel:
            continue
        r = sel[0]
        tw, lw_, n = r["target_wins"], r["wins"] - r["target_wins"], r["games"]
        y = len(HELD_OUT) - 1 - i
        bx.barh(y, 100 * tw / n, color=t["hand"], height=0.42, zorder=3)
        bx.barh(y, 100 * lw_ / n, left=100 * tw / n, color=t["hand"], alpha=0.22, height=0.42, zorder=3, lw=0)
        note = f"{100 * tw / n:.0f}% real wins"
        if round(100 * lw_ / n):
            note += f"  (+{100 * lw_ / n:.0f}% at round limit)"
        bx.text(0, y + 0.29, note, fontsize=11, color=t["ink2"], va="bottom", ha="left", zorder=5,
                bbox=dict(boxstyle="square,pad=0.1", fc=t["bg"], ec="none"))
    bx.axvline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)), zorder=4)
    bx.set_yticks(range(len(HELD_OUT)))
    bx.set_yticklabels([WORLD[g] + ("\n(10 rounds)" if ROUNDS[g] <= 10 else "") for g in reversed(HELD_OUT)],
                       fontsize=12)
    bx.set_ylim(-0.5, len(HELD_OUT) - 0.2)
    bx.set_xlim(0, 100)
    bx.set_xticks([0, 25, 50, 100])
    bx.set_xticklabels(["0", "25%", "50", "100"], fontsize=12)
    bx.set_title("Worlds it never trained on\n(vs 3 rule-based bots)", loc="left", fontsize=14, color=t["ink2"],
                 pad=8)
    cp = can_play_line(MAIN_RUN, best)
    if cp:
        status, games, ended, refused = cp
        fig.text(0.065, 0.115, f"Can it play any world? {games} made-up worlds at 2 to 6 seats: "
                 f"{'all' if ended == games else ended} finished, {refused} illegal moves.", fontsize=13,
                 color=t["ink"])

    # Sonnet: three Sonnet seats against one bot seat, Tutorial Island
    rows_s = []
    for steps, name in SONNET_ROWS:
        for arm in ("restricted", "full"):
            r = [q for q in sonnet if q["steps"] == steps and q["arm"] == arm]
            if r:
                rows_s.append((name + ("" if arm == "restricted" else ", full game"), r[0], arm))
    for i, (name, r, arm) in enumerate(rows_s):
        y = len(rows_s) - 1 - i
        lo, hi = wilson(r["wins"], r["games"])
        p_ = 100 * r["wins"] / r["games"]
        sx.plot([100 * lo, 100 * hi], [y, y], color=t["sonnet"], lw=2, alpha=0.45, solid_capstyle="round")
        sx.plot([p_], [y], "D", ms=9, color=t["sonnet"], mfc=t["sonnet"] if arm == "restricted" else t["bg"],
                mec=t["sonnet"], mew=2, zorder=5)
        sx.text(100 * hi + 3, y, f"{r['wins']}/{r['games']}", fontsize=11, color=t["ink2"], va="center")
    sx.axvline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)))
    sx.set_yticks(range(len(rows_s)))
    sx.set_yticklabels([n for n, _, _ in reversed(rows_s)], fontsize=12)
    sx.set_ylim(-0.6, max(len(rows_s), 1) - 0.4)
    sx.set_xlim(0, 100)
    sx.set_xticks([0, 25, 50, 100])
    sx.set_xticklabels(["0", "25%", "50", "100"], fontsize=12)
    sx.set_title("vs 3 Claude Sonnet seats\n(Island; only our bot's moves)", loc="left", fontsize=14,
                 color=t["ink2"], pad=8)

    # title and footnote
    h = main["hand"]
    if h:
        best_pt = max(h, key=lambda s: s[1])
        beats = bool(ref) and best_pt[2] > ref[0][3]       # its interval clears the rule-based bot's own
        verdict = "beating the bot it copied" if beats else "level with the bot it copied"
        fig.text(0.065, 0.93, f"PPO lifts our bot from {100 * h[0][1]:.0f}% to {100 * h[-1][1]:.0f}%, {verdict}",
                 fontsize=26, fontweight="bold", color=t["ink"])
    fig.text(0.065, 0.875, "Warm-started by imitating our rule-based bot, then PPO against itself and an evolved rival*. "
             "95% intervals; 800 games per point.", fontsize=15, color=t["ink2"])
    foot = ("* Evolved rival: made by evolutionary program synthesis [read: Claude keeps rewriting the bot and we keep "
            "whatever wins]. It trades in training; here it plays with trading off, since our bot can't trade.\n"
            "Our bot never proposes laws, talks or trades with players; it votes by the rule-based bot's rule. "
            "Wins at the round limit don't count as strength. Sonnet: our bot in every seat in turn; bars are wide.")
    fig.text(0.065, 0.025, foot, fontsize=10.5, color=t["muted"], va="bottom", linespacing=1.5)
    for path in out_paths:
        fig.savefig(path, facecolor=t["bg"], dpi=120)
    plt.close(fig)


def main():
    rows = load_eval()
    sonnet = load_sonnet()
    draw("light", rows, sonnet, [os.path.join(HERE, "hero.png"), os.path.join(HERE, "hero.svg")])
    draw("dark", rows, sonnet, [os.path.join(HERE, "hero-dark.png")])
    for o in ("random", "hand", "champion-closed"):
        for run in (MAIN_RUN, SCRATCH_RUN):
            s = series(rows, run, o, TRAIN)
            if s:
                print(run, o, " ".join(f"{p[0] / 1e6:.1f}M:{100 * p[1]:.1f}({100 * p[2]:.1f}-{100 * p[3]:.1f})"
                                       for p in s))


if __name__ == "__main__":
    main()
