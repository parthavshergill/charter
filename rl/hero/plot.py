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
LABEL = {"random": "vs 3 random players", "hand": "vs 3 of the bot it copied",
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


SONNET_LABEL = {"hv2-0": 0, "hv2-9.8M": 9830400, "hv2-29.5M": 29491200, "hv2-97.3M": 97320960}


def style(a, t):
    a.set_facecolor(t["bg"])
    for side in ("top", "right"):
        a.spines[side].set_visible(False)
    a.tick_params(length=0)


def draw(theme_name, rows, sonnet, out_paths):
    """One chart: the main run against three kinds of bot, and Sonnet seats at the same run's checkpoints."""
    t = THEMES[theme_name]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 16, "text.color": t["ink"],
                         "axes.labelcolor": t["ink2"], "xtick.color": t["ink2"], "ytick.color": t["ink2"],
                         "axes.edgecolor": t["grid"], "svg.fonttype": "none"})
    fig = plt.figure(figsize=(16, 9), facecolor=t["bg"])
    ax = fig.add_axes([0.07, 0.25, 0.62, 0.56])
    style(ax, t)
    M = 1e6
    main = {o: series(rows, MAIN_RUN, o, TRAIN) for o in ("random", "hand", "champion-closed")}
    xmax = max([q[0] for s in main.values() for q in s] + [max(SONNET_LABEL.values())]) / M + 3

    ax.axhline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)), zorder=1)
    labels = [(25, "25%  an equal player", t["ink2"], "normal", t["ink2"])]
    for o, s in main.items():
        if not s:
            continue
        xs = [q[0] / M for q in s]
        ax.fill_between(xs, [100 * q[2] for q in s], [100 * q[3] for q in s], color=t[o], alpha=0.18, lw=0, zorder=2)
        ax.plot(xs, [100 * q[1] for q in s], color=t[o], lw=3, zorder=3, solid_capstyle="round")
        ax.plot(xs, [100 * q[1] for q in s], "o", color=t[o], ms=7, mec=t["bg"], mew=1.5, zorder=4)
        y = 100 * s[-1][1]
        labels.append((y, f"{y:.0f}%  {LABEL[o]}", t["ink"], "bold" if o == "hand" else "normal", t[o]))

    # Sonnet seats against checkpoints of this same run: diamonds with 95% intervals
    pts = sorted((r for r in sonnet if r["arm"] == "restricted" and r.get("run") == MAIN_RUN),
                 key=lambda r: r["steps"])
    for r in pts:
        lo, hi = wilson(r["wins"], r["games"])
        x, y = r["steps"] / M, 100 * r["wins"] / r["games"]
        ax.plot([x, x], [100 * lo, 100 * hi], color=t["sonnet"], lw=2, alpha=0.5, zorder=5, solid_capstyle="round")
        ax.plot([x], [y], "D", ms=12, color=t["sonnet"], mec=t["bg"], mew=1.5, zorder=6, clip_on=False)
        if r is pts[-1]:
            continue        # the label column names the last point
        right = False
        ax.text(x - 1.5 if right else x + 1.5, y, f"{r['wins']}/{r['games']}", color=t["sonnet"], fontsize=13,
                va="center", ha="right" if right else "left", zorder=6)
    if pts:
        r = pts[-1]
        y = 100 * r["wins"] / r["games"]
        n = sum(q["games"] for q in pts)
        labels.append((y, f"{r['wins']}/{r['games']} wins vs 3 Claude Sonnet seats", t["sonnet"], "bold", t["sonnet"],
                       r["steps"] / M + 1.5))

    placed = []
    for y, text, color, weight, mark, *anchor in sorted(labels, key=lambda l: -l[0]):
        ly = min([y] + [q - 5 for q in placed])
        placed.append(ly)
        ax.annotate(text, xy=(anchor[0] if anchor else xmax, y), xytext=(xmax + 3, ly), color=color, fontsize=15, fontweight=weight,
                    va="center", ha="left", annotation_clip=False,
                    arrowprops=dict(arrowstyle="-", color=mark, lw=1, shrinkA=0, shrinkB=0))

    if main["hand"]:
        ax.annotate("start: imitation of\na rule-based bot", xy=(0, 100 * main["hand"][0][1]), xytext=(32, 6),
                    color=t["ink2"], fontsize=13, arrowprops=dict(arrowstyle="-", color=t["muted"], lw=1))
    ax.set_xlim(-2, xmax)
    ax.set_ylim(0, 102)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_yticklabels(["0%", "25%", "50%", "75%", "100%"])
    ax.set_xlabel("PPO training steps (millions)")
    ax.set_ylabel("win rate: our bot vs 3 opponents")
    ax.grid(axis="y", color=t["grid"], lw=1)
    ax.set_axisbelow(True)

    h = main["hand"]
    if h:
        ref = series(rows, REF_RUN, "hand", TRAIN)
        best_pt = max(h, key=lambda s: s[1])
        beats = bool(ref) and best_pt[2] > ref[0][3]       # its interval clears the rule-based bot's own
        verdict = "now beats the rule-based bot it copied" if beats else "now level with the bot it copied"
        fig.text(0.07, 0.92, f"Trained with PPO, our bot {verdict}", fontsize=28, fontweight="bold", color=t["ink"])
    fig.text(0.07, 0.865, "Charter, 4 players. Warm-started by copying an older rule-based bot, then trained against "
             "itself and an evolved rival*.", fontsize=16, color=t["ink2"])
    n_s = sum(r["games"] for r in pts)
    foot = ("* Evolved by program synthesis [read: Claude keeps rewriting the bot and we keep whatever wins].\n"
            "The bot it copied is an older rule-based bot. The bot at our tables today is stronger: our best "
            "checkpoint wins 24% against it (PR #31).\n"
            "Bot games: 800 per point on Island and Not Catan, with 95% intervals.\n"
            f"Sonnet: {n_s} games on Island, our bot in every seat in turn. Sonnet gets only our bot's moves "
            "(no laws, talk or player trades). Small samples, so wide bars.")
    fig.text(0.07, 0.025, foot, fontsize=12, color=t["muted"], va="bottom", linespacing=1.6)
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
