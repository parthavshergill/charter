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
MAIN_RUN = "v2-fix"           # imitation warm start, then PPO; waiting-row fix; hand bots in 50% of games
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


def draw(theme_name, rows, sonnet, out_paths):
    t = THEMES[theme_name]
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 15, "text.color": t["ink"],
                         "axes.labelcolor": t["ink2"], "xtick.color": t["ink2"], "ytick.color": t["ink2"],
                         "axes.edgecolor": t["grid"], "svg.fonttype": "none"})
    fig = plt.figure(figsize=(16, 9), facecolor=t["bg"])
    gs = fig.add_gridspec(1, 2, width_ratios=[2.15, 1], left=0.065, right=0.975, top=0.80, bottom=0.27, wspace=0.33)
    ax = fig.add_subplot(gs[0])
    bx = fig.add_subplot(gs[1])
    for a in (ax, bx):
        a.set_facecolor(t["bg"])
        for side in ("top", "right"):
            a.spines[side].set_visible(False)
        a.tick_params(length=0)

    M = 1e6
    main = {o: series(rows, MAIN_RUN, o, TRAIN) for o in ("random", "hand", "champion-closed")}
    last_x = max((p[0] for s in main.values() for p in s), default=60 * M) / M

    # equal-player line
    ax.axhline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)), zorder=1)
    ax.text(6.5, 26.3, "equal player: 25%", color=t["ink2"], fontsize=14, ha="left", va="bottom")

    # from-scratch PPO, same network, a separate run: grey dotted lines
    scratch = {o: series(rows, SCRATCH_RUN, o, TRAIN) for o in ("random", "hand")}
    for o, s in scratch.items():
        if s:
            ax.plot([p[0] / M for p in s], [100 * p[1] for p in s], color=t["muted"], lw=2, ls=(0, (1, 2.2)),
                    zorder=2, dash_capstyle="round")
    if scratch["random"] and scratch["hand"]:
        r, h = scratch["random"][-1], scratch["hand"][-1]
        ax.annotate(f"dotted: the same network trained with PPO from scratch\n(a separate run): "
                    f"{100 * r[1]:.0f}% vs random, {100 * h[1]:.0f}% vs rule-based bots",
                    xy=(r[0] / M * 0.62, 100 * scratch["random"][-2][1] + 0.5), xytext=(14, 55), color=t["ink2"],
                    fontsize=12.5, arrowprops=dict(arrowstyle="-", color=t["muted"], lw=1))

    # the main run
    ends = []
    for o, s in main.items():
        if not s:
            continue
        xs = [p[0] / M for p in s]
        ax.fill_between(xs, [100 * p[2] for p in s], [100 * p[3] for p in s], color=t[o], alpha=0.18, lw=0, zorder=2)
        ax.plot(xs, [100 * p[1] for p in s], color=t[o], lw=2.6, zorder=3, solid_capstyle="round")
        ax.plot(xs, [100 * p[1] for p in s], "o", color=t[o], ms=6, mec=t["bg"], mew=1.5, zorder=4)
        ends.append((o, xs[-1], 100 * s[-1][1]))
    placed = []
    for o, x, y in sorted(ends, key=lambda e: -e[2]):
        ly = y
        for q in placed:          # keep labels at least 6 points apart
            ly = min(ly, q - 6)
        placed.append(ly)
        ax.text(x + 1.0, ly, f"{y:.0f}%  {LABEL[o]}", color=t["ink"], fontsize=14, ha="left", va="center",
                fontweight="bold" if o == "hand" else "normal")

    # Sonnet points
    for arm, marker, fill in (("restricted", "D", True), ("full", "D", False)):
        pts = [r for r in sonnet if r["arm"] == arm]
        for r in pts:
            lo, hi = wilson(r["wins"], r["games"])
            p = 100 * r["wins"] / r["games"]
            x = r["steps"] / M + (0.9 if arm == "full" else 0)
            ax.errorbar([x], [p], yerr=[[p - 100 * lo], [100 * hi - p]], fmt=marker, ms=10, color=t["sonnet"],
                        mfc=t["sonnet"] if fill else t["bg"], mec=t["sonnet"], mew=2, elinewidth=1.6, capsize=4,
                        zorder=5)
        if pts:
            r = max(pts, key=lambda r: r["steps"])
            n = sum(q["games"] for q in pts)
            name = "vs 3 Sonnet, same moves as the bot" if arm == "restricted" else "vs 3 Sonnet, full game"
            ax.text(r["steps"] / M + (2.2 if arm == "full" else 1.3), 100 * r["wins"] / r["games"],
                    f"{name}\n({n} games, wide bars)", color=t["sonnet"], fontsize=12, va="center")

    ax.annotate("start: imitation of\nour rule-based bot", xy=(0, 100 * main["hand"][0][1]) if main["hand"] else (0, 10),
                xytext=(1.5, 36), color=t["ink2"], fontsize=12,
                arrowprops=dict(arrowstyle="-", color=t["muted"], lw=1))
    ax.set_xlim(-1.5, last_x * 1.42)
    ax.set_ylim(0, 102)
    ax.set_yticks([0, 25, 50, 75, 100])
    ax.set_yticklabels(["0%", "25%", "50%", "75%", "100%"])
    ax.set_xlabel("PPO training steps (millions)")
    ax.set_ylabel("win rate, 1 bot vs 3 opponents")
    ax.grid(axis="y", color=t["grid"], lw=1)
    ax.set_axisbelow(True)
    ax.set_title("Training worlds (Island, Not Catan)", loc="left", fontsize=15, color=t["ink2"], pad=10)

    # panel 2: worlds it never trained on, best checkpoint, vs our rule-based bots
    best = main["hand"][-1][0] if main["hand"] else None
    worlds = list(HELD_OUT)
    for i, g in enumerate(worlds):
        sel = [r for r in rows if r["run"] == MAIN_RUN and r["steps"] == best and r["game"] == g
               and r["opponent"] == "hand"]
        if not sel:
            continue
        r = sel[0]
        tw, lw_, n = r["target_wins"], r["wins"] - r["target_wins"], r["games"]
        y = len(worlds) - 1 - i
        bx.barh(y, 100 * tw / n, color=t["hand"], height=0.42, zorder=3)
        bx.barh(y, 100 * lw_ / n, left=100 * tw / n, color=t["hand"], alpha=0.22, height=0.42, zorder=3, lw=0)
        note = f"{100 * tw / n:.0f}% real wins"
        if round(100 * lw_ / n):
            note += f"  (+{100 * lw_ / n:.0f}% at the round limit)"
        bx.text(0, y + 0.29, note, fontsize=12, color=t["ink2"], va="bottom", ha="left", zorder=5,
                bbox=dict(boxstyle="square,pad=0.1", fc=t["bg"], ec="none"))
    bx.axvline(25, color=t["ink2"], lw=1.5, ls=(0, (4, 3)), zorder=4)
    bx.set_yticks(range(len(worlds)))
    bx.set_yticklabels([WORLD[g] + ("\n(10 rounds)" if ROUNDS[g] <= 10 else "") for g in reversed(worlds)],
                       fontsize=13)
    bx.set_ylim(-0.5, len(worlds) - 0.2)
    bx.set_xlim(0, 100)
    bx.set_xticks([0, 25, 50, 100])
    bx.set_xticklabels(["0", "25%", "50", "100"])
    bx.set_xlabel("win rate vs 3 rule-based bots")
    bx.set_title("Worlds it never trained on", loc="left", fontsize=15, color=t["ink2"], pad=10)
    cp = can_play_line(MAIN_RUN, best)
    if cp:
        status, games, ended, refused = cp
        bx.text(-0.02, -0.16, f"Can it play any world? {games} made-up worlds,\n"
                f"2 to 6 seats: {'all' if ended == games else ended} finished, {refused} illegal moves", fontsize=13, color=t["ink"], va="top",
                transform=bx.transAxes, linespacing=1.4)

    # title and footnote
    h = main["hand"]
    if h:
        fig.text(0.065, 0.93, f"PPO lifts our bot from {100 * h[0][1]:.0f}% to {100 * h[-1][1]:.0f}%, level with the bot it copied", fontsize=26, fontweight="bold", color=t["ink"])
    fig.text(0.065, 0.875, "Warm-started by imitating our rule-based bot, then trained with PPO against itself and that "
             "bot. 95% intervals; 800 games per point.", fontsize=15, color=t["ink2"])
    foot = ("* Evolved rival: never seen in training. Made by evolutionary program synthesis [read: Claude keeps rewriting the "
            "bot and we keep whatever wins].\nShown with trading off, since our bot can't trade. "
            "Our bot never proposes laws, talks or trades with players; it votes by the rule-based bot's rule.\n"
            "Wins at the round limit (most of them on the 10-round worlds) don't count as strength.")
    if sonnet:
        foot += ("\nSonnet points: Claude Sonnet subagents playing seats over HTTP; 'same moves' limits them in code "
                 "to the bot's moves, 'full game' lets them talk, trade and propose laws.")
    fig.text(0.065, 0.025, foot, fontsize=11, color=t["muted"], va="bottom", linespacing=1.5)
    for p in out_paths:
        fig.savefig(p, facecolor=t["bg"], dpi=120)
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
