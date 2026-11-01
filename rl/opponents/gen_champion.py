"""Write rl/lean/CharterRL/Champion.lean from night2_champion.lean and night2_champion.json.

    python3 rl/opponents/gen_champion.py          # write it
    python3 rl/opponents/gen_champion.py --check  # fail if the file differs from what this would write

The strategy's code is copied as it is, in the namespace `CharterRL.Champion`, so that it lives only in the training
library and never in the server's build. The JSON's weights become a `Weights` value: names that are fields of
`Weights` set those fields, and the rest go to `extra`, where the strategy reads them with `extraOr`.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "..", "lean", "CharterRL", "Champion.lean")
# The fields of `CharterServer.Bots.Weights` (Server/BotCore.lean). Every other name is an extra.
FIELDS = ["pipValue", "resourceBonus", "roadStepPenalty", "prioUpgrade", "prioSpot", "prioAttach", "prioRoad",
          "roadWithSite", "bankTradeOn", "acceptGoods", "acceptNeed", "acceptScarcity", "acceptOtherPoints",
          "acceptMargin", "offerLimit", "offerGive", "voteMargin", "dealMargin"]


# Rewrites that make the copy faster and change nothing it decides. `charter-rl-check` plays games with this copy and
# with the untouched one (`champion-ref`) side by side, and they must be the same.
# 1. `pips` works out the whole dice table for each number it is asked about. The scoring asks for every tile of every
#    spot, so the table is made once per scoring (`pipsTable`) and read (`pipsT`); `incomeOfT` is `incomeOf` reading
#    it. The paying regions (`paidRegions G`) are also listed once per scoring, not once per spot.
# 2. `evDecide` asks `reactions` for votes, signatures and accepts, then drops the accepts. `votesAndSigns` is the part
#    of `reactions` that makes votes and signatures, in the same order.
HELPERS = """
/-- The dice's ways to make each total, worked out once: `pipsT t n` is `CharterServer.Bots.pips G n`, which is
`(Scene.diceWays G).getD n 0`. -/
def pipsTable (G : GameDef) : Array Nat := (Scene.diceWays G).toArray

@[inline] def pipsT (t : Array Nat) (n : Nat) : Nat := t.getD n 0

/-- `CharterServer.Bots.incomeOf`, reading the dice table. -/
def incomeOfT {G : GameDef} (pt : Array Nat) (s : State G) (p : Nat) (r : Res) : Nat :=
  let rules := s.rules
  let mine := s.pieces.filter (·.owner == p)
  ((paidRegions G).filter (·.res == r)).foldl (fun acc reg =>
    acc + pipsT pt reg.number * (mine.foldl (fun n x => match x.loc with
      | .spot v =>
        if reg.spots.contains v then n + ((rules.piece? x.kind).map (·.yield)).getD 0 else n
      | .link _ => n) 0)) 0

/-- The votes and signatures of `CharterServer.Bots.reactions`, in its order, without its accepts. -/
def votesAndSigns {G : GameDef} (ctx : Ctx G) (s : State G) (bots : List Nat) : List Event := Id.run do
  let mut out : Array Event := #[]
  for p in s.openProposals do
    for b in bots do
      match p.body with
      | .law L =>
        if !(p.votes.any (·.1 == b)) then
          out := out.push (.vote b p.id (lawOk ctx s b p.id L))
      | .deal d =>
        if d.signers.contains b && !p.signed.contains b && dealOk ctx b d then
          out := out.push (.sign b p.id)
  return out.toList
"""

FAST = [
    ("def evTouch {G : GameDef} (_ctx : Ctx G) (v : Nat) : List (Res × Nat) :=\n  (paidRegions G).filterMap fun r =>",
     "def evTouch {G : GameDef} (pt : Array Nat) (paid : List Region) (_ctx : Ctx G) (v : Nat) : List (Res × Nat) :=\n"
     "  paid.filterMap fun r =>"),
    ("if r.spots.contains v then some (r.res, CharterServer.Bots.pips G r.number) else none",
     "if r.spots.contains v then some (r.res, pipsT pt r.number) else none"),
    ("def evSupply {G : GameDef} (_ctx : Ctx G) (r : Res) : Nat :=\n"
     "  ((paidRegions G).filter (·.res == r)).foldl (fun a reg => a + CharterServer.Bots.pips G reg.number) 0",
     "def evSupply {G : GameDef} (pt : Array Nat) (paid : List Region) (_ctx : Ctx G) (r : Res) : Nat :=\n"
     "  (paid.filter (·.res == r)).foldl (fun a reg => a + pipsT pt reg.number) 0"),
    ("  let W := ctx.weights\n  let newB := W.extraOr \"newKindBonus\" 6",
     "  let W := ctx.weights\n  let pt := pipsTable G\n  let paid := paidRegions G\n  let newB := W.extraOr \"newKindBonus\" 6"),
    ("let inc : List (Res × Nat) := names.map fun r => (r, incomeOf s p r)",
     "let inc : List (Res × Nat) := names.map fun r => (r, incomeOfT pt s p r)"),
    ("let sup : List (Res × Nat) := names.map fun r => (r, evSupply ctx r)",
     "let sup : List (Res × Nat) := names.map fun r => (r, evSupply pt paid ctx r)"),
    ("let ts := evTouch ctx v", "let ts := evTouch pt paid ctx v"),
    ("let props := (reactions ctx s [seat]).filter fun e => match e with",
     "let props := (votesAndSigns ctx s [seat]).filter fun e => match e with"),
]
# Rewrites that may match more than once: every one is replaced.
FAST_ALL = [
    ("bestBy short (fun r => -(incomeOf s p r : Int))", "bestBy short (fun r => -(incomeOfT (pipsTable G) s p r : Int))"),
]


def weights_text(meta):
    weights = dict(meta["weights"])
    for c in meta.get("constants", []):
        weights.setdefault(c["name"], c["default"])
    fields = [f"{k} := {weights[k]}" for k in FIELDS if k in weights]
    extra = ", ".join(f'("{k}", {v})' for k, v in sorted(weights.items()) if k not in FIELDS)
    return f"""
/-- The weights of `{meta['id']}`, from `night2_champion.json`. -/
def weights : Weights :=
  {{ {", ".join(fields)}
    extra := [{extra}] }}

/-- The same strategy, making no offers and accepting none. -/
def closedWeights : Weights :=
  {{ weights with extra := weights.extra.map fun (k, v) =>
      if k == "myOfferLimit" then (k, 0) else if k == "accMargin" then (k, 1000000) else (k, v) }}
"""


def render():
    src = open(os.path.join(HERE, "night2_champion.lean")).read()
    meta = json.load(open(os.path.join(HERE, "night2_champion.json")))
    old = re.search(r"^namespace (\S+)$", src, re.M).group(1)
    head_end = src.index(f"namespace {old}\n")
    imports, body = src[:head_end], src[head_end + len(f"namespace {old}\n"):]
    body = body.replace(f"end {old}\n", "", 1).rstrip() + "\n"
    opens = re.match(r"(open [^\n]*\n)", body).group(1)
    fast = body
    for a, b in FAST:
        assert fast.count(a) == 1, f"the rewrite expects this exactly once: {a}"
        fast = fast.replace(a, b)
    for a, b in FAST_ALL:
        assert a in fast, f"the rewrite expects this at least once: {a}"
        fast = fast.replace(a, b)
    fast = fast.replace(opens, opens + HELPERS, 1)
    w = weights_text(meta)
    head = ("/- Generated by rl/opponents/gen_champion.py from rl/opponents/night2_champion.lean and .json.\n"
            "   Do not edit: change those files or the script, and run it again. -/\n")
    ref = ("\n/-! The strategy as written, for the test that the fast copy below decides the same. -/\n"
           "namespace CharterRL.ChampionRef\n" + body + w + "\nend CharterRL.ChampionRef\n")
    quick = ("\n/-! The same strategy with the rewrites of `gen_champion.py`, which change nothing it decides. -/\n"
             "namespace CharterRL.Champion\n" + fast + w + "\nend CharterRL.Champion\n")
    return head + imports + ref + quick


def main():
    text = render()
    if "--check" in sys.argv:
        same = os.path.exists(OUT) and open(OUT).read() == text
        print("Champion.lean is up to date" if same else "Champion.lean differs: run rl/opponents/gen_champion.py")
        sys.exit(0 if same else 1)
    open(OUT, "w").write(text)
    print(f"wrote {os.path.relpath(OUT)}")


if __name__ == "__main__":
    main()
