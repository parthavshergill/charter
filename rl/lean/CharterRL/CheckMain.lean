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
  s!"missing={c.missing} declare_not_offered={c.declareNotOffered} move_while_voting={c.moveWhileVoting} " ++
  s!"placements={c.placements} place_overflow={c.placeOverflow} end_in_setup={c.endInSetup}" ++
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
    let e3 := maskTest T policyVotes 4 2 (·.mask) 400 placesDropLast
    report bad (e3.errors > 0) s!"mask {id} seeded error (last placement has no row) caught: {maskLine e3}"
  -- With declare_always, declarations are offered where no law reads them, and the engine takes each one offered.
  for id in trainIds do
    let some T := tablesOf? id | continue
    let c := maskTest T { policyVotes with declareAlways := true } 4 1 (·.mask) 300
    report bad (c.errors == 0 && c.declareNotOffered == 0 && c.offered > 0)
      s!"mask {id} declare_always: {maskLine c}"
  -- The held-out games, more briefly, at every seat count they allow.
  for id in allIds.filter (!trainIds.contains ·) do
    let some T := tablesOf? id | continue
    for seats in (List.range (T.maxSeats + 1)).filter (T.minSeats ≤ ·) do
      let c := maskTest T policyVotes seats 1 (·.mask) 100
      report bad (c.errors == 0 && c.offered > 0) s!"mask {id} (held out), {seats} seats: {maskLine c}"
  -- Can it play: every game, and made-up games at the engine's limits and at odd small sizes, at every seat count,
  -- to the end, with random legal actions.
  let made : List String := ["gen-limits-1", "gen-limits-2", "gen-tiny-1", "gen-tiny-2", "gen-tiny-3"] ++
    (List.range (if quick then 4 else 12)).map (s!"gen-odd-{·}")
  for id in allIds ++ made do
    let T ← match tablesOf? id, Gen.tables? id with
      | some T, _ => pure T
      | none, some (.ok T) => pure T
      | none, some (.error err) => report bad false s!"play {id}: {err}"; continue
      | none, none => report bad false s!"play {id}: no such game"; continue
    report bad T.problems.isEmpty s!"layout {id} fits {T.problems}"
    for seats in (List.range (T.maxSeats + 1)).filter (T.minSeats ≤ ·) do
      let c := playTest T policyVotes seats (if quick then 1 else 2) (if id.startsWith "gen-limits" then 8 else 30)
      let G := T.G
      report bad (c.errors == 0)
        (s!"play {id}, {seats} seats ({G.resources.length} resources, {G.pieces.length} kinds, {G.map.spotCount} spots, " ++
         s!"{G.map.links.length} links, {G.map.regions.length} tiles, {G.foundingLaws.length} founding laws): " ++
         s!"games={c.games} ended={c.ended} decisions={c.decisions} no_action={c.noAction} refused={c.refused} " ++
         s!"stuck={c.stuck} most_places={c.mostPlaces} place_overflow={c.overflow} mask_errors={c.mask.errors}" ++
         (if c.firstError == "" then "" else s!" first_error=\"{c.firstError}\"") ++
         (if c.mask.firstError == "" then "" else s!" mask_error=\"{c.mask.firstError}\""))
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
  -- Votes worked out once per law for all seats give the same games as `lawOk` for each voter.
  for id in allIds do
    let some T := tablesOf? id | continue
    let seats := min 4 T.maxSeats
    let hand := (opponents.find? (·.name == "hand")).get!
    let champ := (opponents.find? (·.name == "champion")).get!
    let mixed : Array SeatPlan := #[{ setup := none, play := none }, { setup := some hand, play := some hand },
      { setup := some champ, play := some champ }] ++ Array.replicate (seats - 3) { setup := none, play := none }
    let botVotes : Settings := { voteMode := .bot, lawEvery := 2 }
    let mut diffs := 0
    let mut n := 0
    for g in [0:(if quick then 3 else 8)] do
      match Env.start T botVotes mixed (600 + g), Env.start T botVotes mixed (600 + g) (shareVotes := false) with
      | .ok a, .ok b =>
        let (d, k) := sideBySide a b (700 + g) 2000
        diffs := diffs + d
        n := n + k
      | _, _ => report bad false s!"shared votes {id}: the game did not start"
    report bad (diffs == 0 && n > 0) s!"shared votes {id}: {diffs} of {n} decisions differ from lawOk per voter"
    -- And a preview worked out once per law gives the same observations as one per voter.
    let mut pd := 0
    let mut pn := 0
    for g in [0:(if quick then 2 else 6)] do
      match Env.start T { policyVotes with lawEvery := 2 } (callers seats) (650 + g),
            Env.start T { policyVotes with lawEvery := 2 } (callers seats) (650 + g) (shareVotes := false) with
      | .ok a, .ok b =>
        let (d, k) := sideBySide a b (750 + g) 1500
        pd := pd + d
        pn := pn + k
      | _, _ => report bad false s!"shared preview {id}: the game did not start"
    report bad (pd == 0 && pn > 0) s!"shared preview {id}: {pd} of {pn} decisions differ from a preview per voter"
  -- The fast champion decides as the champion as written does.
  for id in allIds do
    let some T := tablesOf? id | continue
    let seats := min 4 T.maxSeats
    let byName (n : String) : SeatPlan := let o := (opponents.find? (·.name == n)).get!; { setup := some o, play := some o }
    let lineup (n : String) : Array SeatPlan := #[{ setup := none, play := none }] ++ Array.replicate (seats - 1) (byName n)
    let mut diffs := 0
    let mut n := 0
    for g in [0:(if quick then 3 else 10)] do
      match Env.start T policyVotes (lineup "champion") (800 + g), Env.start T policyVotes (lineup "champion-ref") (800 + g) with
      | .ok a, .ok b =>
        let (d, k) := sideBySide a b (810 + g) 2000
        diffs := diffs + d
        n := n + k
      | _, _ => report bad false s!"champion {id}: the game did not start"
    report bad (diffs == 0 && n > 0) s!"champion {id}: {diffs} of {n} decisions differ from the champion as written"
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
        , ("self-play, most seats, mask and obs", ({} : Settings), callers T.maxSeats, true)
        , ("self-play, mask and obs, no preview", ({ preview := false } : Settings), callers 4, true)
        , ("self-play, mask and obs, no laws", ({ lawEvery := 0 } : Settings), callers 4, true)
        , ("one seat against 3 hand, mask and obs", ({ voteMode := .bot } : Settings), vsHand, true) ] do
      let (dps, gps, n) ← speed T st lineup (if quick then 4 else 20) obs
      line s!"SPEED {id} {name}: {fmt dps} decisions/s, {fmt gps} games/s, {n} decisions"
  let n ← bad.get
  line (if n == 0 then "ALL PASS" else s!"{n} FAILED")
  return if n == 0 then 0 else 1
