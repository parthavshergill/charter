import CharterRL.Check

/-!
# `charter-rl-check`

Runs the tests of `CharterRL.Check` and prints one line per result. Exits 1 if any test fails, including a seeded
error that is not caught. `--quick` plays fewer games. `--layout PATH` writes `rl/layout.json` and stops.
-/

open Lean CharterRL CharterRL.Check

/-- Print a result and count it if it failed. -/
def report (bad : IO.Ref Nat) (ok : Bool) (what : String) : IO Unit := do
  line s!"{if ok then "PASS" else "FAIL"} {what}"
  if !ok then bad.modify (· + 1)

def maskLine (c : MaskCount) : String :=
  s!"decisions={c.decisions} actions={c.actions} offered={c.offered} offered_refused={c.offeredRefused} " ++
  s!"missing={c.missing} declare_not_offered={c.declareNotOffered} move_while_voting={c.moveWhileVoting}" ++
  (if c.firstError == "" then "" else s!" first_error=\"{c.firstError}\"")

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--layout", path] =>
    IO.FS.writeFile path (layoutJson.pretty ++ "\n")
    return 0
  | _ => pure ()
  let quick := args.contains "--quick"
  let games := if quick then 3 else 12
  let bad ← IO.mkRef 0
  let policyVotes : Settings := { voteMode := .policy, lawEvery := 3 }
  let trainIds := ["island", "not-catan"]
  let allIds := allTables.toList.map (·.id)
  -- Every game fits the layout.
  for T in allTables do
    report bad T.problems.isEmpty s!"layout {T.id} fits {T.problems}"
  -- The mask against the engine.
  for id in trainIds do
    let some T := tablesOf? id | report bad false s!"no game {id}"; continue
    for (name, st) in [("laws by policy", policyVotes), ("no laws", ({ lawEvery := 0 } : Settings))] do
      let c := maskTest T st 4 games (·.mask)
      report bad (c.errors == 0 && c.offered > 0) s!"mask {id} {name}: {maskLine c}"
    let e1 := maskTest T policyVotes 4 2 maskEndAlways
    report bad (e1.errors > 0) s!"mask {id} seeded error (end turn always offered) caught: {maskLine e1}"
    let e2 := maskTest T policyVotes 4 2 maskDropLast
    report bad (e2.errors > 0) s!"mask {id} seeded error (last action dropped) caught: {maskLine e2}"
  -- The held-out games, more briefly.
  for id in allIds.filter (!trainIds.contains ·) do
    let some T := tablesOf? id | continue
    let seats := min 4 T.maxSeats
    let c := maskTest T policyVotes seats 2 (·.mask) 150
    report bad (c.errors == 0 && c.offered > 0) s!"mask {id} (held out): {maskLine c}"
  -- Determinism, the seed, renaming.
  for id in allIds do
    let some T := tablesOf? id | continue
    let seats := min 4 T.maxSeats
    let withRows : Settings := { policyVotes with moveRows := true }
    for g in [0:(if quick then 1 else 3)] do
      match Env.start T withRows (callers seats) (300 + g), Env.start T withRows (callers seats) (300 + g) with
      | .ok a, .ok b =>
        let (d, n) := sideBySide a b (900 + g)
        report bad (d == 0) s!"determinism {id} seed {300 + g}: {d} of {n} decisions differ"
        let (d, n) := sideBySide a a (900 + g) 400 reseeded
        report bad (d == 0) s!"seed blind {id} seed {300 + g}: {d} of {n} observations change with State.seed"
      | _, _ => report bad false s!"determinism {id}: the game did not start"
    match Env.start T policyVotes (callers seats) 41, renamedEnv T policyVotes seats 41 with
    | .ok a, .ok b =>
      let (d, n) := sideBySide a b 17
      report bad (d == 0) s!"renaming {id}: {d} of {n} decisions differ"
    | .error e, _ | _, .error e => report bad false s!"renaming {id}: {e}"
    -- Seeded error for the seed test: the dice of the next roll, as a seat should never see them.
    match Env.start T policyVotes (callers seats) 43 with
    | .ok a =>
      let peek (e : Env) : Env :=
        let s := e.play.state
        { e with base := e.base.set! 0 (Float.ofNat (Charter.rollAt e.G s.seed s.rollsMade)) }
      let (d, n) := sideBySide a a 19 400 (fun e => peek (reseeded e)) peek
      let (d0, _) := sideBySide a a 19 400 peek peek
      report bad (d > 0 && d0 == 0) s!"seed blind {id} seeded error (next roll shown) caught: {d} of {n} differ"
    | .error e => report bad false s!"seed blind {id} seeded: {e}"
    match Env.start T { policyVotes with slotOrder := .game } (callers seats) 41,
          renamedEnv T { policyVotes with slotOrder := .game } seats 41 true with
    | .ok a, .ok b =>
      let (d, n) := sideBySide a b 17
      report bad (d > 0) s!"renaming {id} seeded error (rows follow the game's list order) caught: {d} of {n} differ"
    | .error e, _ | _, .error e => report bad false s!"renaming {id} seeded: {e}"
  -- Random maps pass the full checks.
  for id in allIds do
    let some T := tablesOf? id | continue
    let n := if quick then 5 else 30
    let ok := (List.range n).all fun i => (randomMap T.G (7000 + i)).checks
    report bad ok s!"maps {id}: {n} random maps pass G.checks"
  -- Speed, one thread.
  for id in trainIds do
    let some T := tablesOf? id | continue
    let hand := (opponents.find? (·.name == "hand")).get!
    let vsHand : Array SeatPlan := #[{ setup := none, play := none }] ++ Array.replicate 3 { setup := some hand, play := some hand }
    for (name, st, lineup, obs) in
        [ ("self-play, mask only", ({} : Settings), callers 4, false)
        , ("self-play, mask and obs", ({} : Settings), callers 4, true)
        , ("self-play, mask and obs, move rows", ({ moveRows := true } : Settings), callers 4, true)
        , ("self-play, mask and obs, no preview", ({ preview := false } : Settings), callers 4, true)
        , ("self-play, mask and obs, no laws", ({ lawEvery := 0 } : Settings), callers 4, true)
        , ("one seat against 3 hand, mask and obs", ({ voteMode := .bot } : Settings), vsHand, true) ] do
      let (dps, gps, n) ← speed T st lineup (if quick then 4 else 20) obs
      line s!"SPEED {id} {name}: {fmt dps} decisions/s, {fmt gps} games/s, {n} decisions"
  let n ← bad.get
  line (if n == 0 then "ALL PASS" else s!"{n} FAILED")
  return if n == 0 then 0 else 1
