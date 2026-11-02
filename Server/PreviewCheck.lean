import Server.Game
import Server.Player
import Server.Preview
import Server.Rules

/-!
# Is the preview true?

This plays real games through `Engine.step`. At many points in each game a seat proposes a law, the
table votes it in, and the turn ends or the seat builds. The check compares the figures the preview gave
at the vote with the entries the engine really made, against the same event played without the law.

`Preview` calls the functions the commandments state, so this does not repeat a proof. It checks that
the preview uses them correctly: the right state, the right order, and the right split of a last turn.

`charter-sim --check-previews` runs it, and `make smoke` calls that. It runs natively, since this many
games are too slow to run while `lake build` checks a file.
-/

namespace CharterServer.PreviewCheck
open Lean Charter CharterServer.Game CharterServer.Preview

variable {G : GameDef}

/-- Add up rows by account and resource, leaving out zeros. -/
def total (rows : List Row) : List Row :=
  let keys := (rows.map fun r => (r.who, r.res)).eraseDups
  keys.filterMap fun (who, res) =>
    let d : Int := ((rows.filter fun r => r.who == who && r.res == res).map (·.delta)).foldl (· + ·) 0
    if d == 0 then none else some { who, res, delta := d }

/-- The same rows, in any order. -/
def sameRows (a b : List Row) : Bool :=
  let x := total a
  let y := total b
  x.length == y.length && x.all (y.contains ·)

/-- What the engine really did with the law, against what it did without it. -/
def actualRows (s : State G) (withLaw without : List Entry) : List Row := rowsOf s without withLaw

/-- Laws to try, by game. They read holdings, act at a round's end, change prices, make pieces and react
to the roll. -/
def lawsFor (spec : GameSpec) : List String :=
  if spec.id == hillSpec.id then
    [ "(law \"Half on a potluck\" (on-build potluck (transfer actor treasury cash (/ (holding actor cash) 2))))"
    , "(law \"Half on a chat\" (on-build chat (transfer actor treasury gas (/ (holding actor gas) 2))))"
    , "(law \"Half on a booth\" (on-build booth (transfer actor treasury boba (/ (holding actor boba) 2))))"
    , "(law \"Gas levy\" (on-round-end (for-each-player true (transfer each treasury gas (/ (holding each gas) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap chats\" (set-cost chat (bundle (boba 1))))"
    , "(law \"Refunds\" (on-round-end (for-each-player (<= 1 (declared each down)) (transfer treasury each cash 1))))"
    , "(law \"Rideshare\" (on-roll (transfer bank actor gas 1)))"
    , "(law \"Taco stands\" (new-piece taco-stand (bundle (takeout 2) (gas 1)) (points 2) (attach booth) (yield 1) (limit 2)))" ]
  else if spec.id == strikeSpec.id then
    [ "(law \"Half on a workshop\" (on-build workshop (transfer actor treasury ore (/ (holding actor ore) 2))))"
    , "(law \"Half on a tunnel\" (on-build tunnel (transfer actor treasury ember (/ (holding actor ember) 2))))"
    , "(law \"Half on a hall\" (on-build hall (transfer actor treasury fungus (/ (holding actor fungus) 2))))"
    , "(law \"Ember levy\" (on-round-end (for-each-player true (transfer each treasury ember (/ (holding each ember) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap tunnels\" (set-cost tunnel (bundle (stone 1))))"
    , "(law \"Danger pays\" (on-round-end (for-each-player (<= 3 (holding treasury danger)) (transfer bank each renown 1))))"
    , "(law \"Vaults\" (new-piece vault (bundle (stone 2) (ore 1)) (points 2) (attach hall) (yield 1) (limit 2)))" ]
  else if spec.id == slimeSpec.id then
    [ "(law \"Half on a swelling\" (on-build swelling (transfer actor treasury oatmeal (/ (holding actor oatmeal) 2))))"
    , "(law \"Half on a tendril\" (on-build tendril (transfer actor treasury dew (/ (holding actor dew) 2))))"
    , "(law \"Half on a node\" (on-build node (transfer actor treasury rot (/ (holding actor rot) 2))))"
    , "(law \"Rot levy\" (on-round-end (for-each-player true (transfer each treasury rot (/ (holding each rot) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap tendrils\" (set-cost tendril (bundle (oatmeal 1))))"
    , "(law \"Sporangia\" (new-piece sporangium (bundle (pollen 2) (rot 1)) (points 2) (attach node) (yield 1) (limit 2)))" ]
  else if spec.id == bubbleSpec.id then
    [ "(law \"Half on a campus\" (on-build campus (transfer actor treasury capital (/ (holding actor capital) 2))))"
    , "(law \"Half on a datacenter\" (on-build datacenter (transfer actor treasury capital (/ (holding actor capital) 2))))"
    , "(law \"Fibre tax\" (on-build fibre (transfer actor treasury concrete 1)))"
    , "(law \"Capital levy\" (on-round-end (for-each-player true (transfer each treasury capital (/ (holding each capital) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap fibre\" (set-cost fibre (bundle (concrete 1))))"
    , "(law \"Emergency audit\" (now (for-each-player true (transfer each bank hype (holding each hype))) (transfer treasury bank bubble (holding treasury bubble))))"
    , "(law \"Margin call\" (on-roll (for-each-player (<= 10 rolled) (transfer each treasury hype (/ (holding each hype) 2)))))"
    , "(law \"Bailout\" (on-round-end (for-each-player (< (points each) 5) (transfer bank each capital 3))))"
    , "(law \"Radomes\" (new-piece radome (bundle (silicon 2) (capital 2)) (points 2) (attach datacenter) (yield 1) (limit 2)))" ]
  else if spec.id == pirateSpec.id then
    [ "(law \"Half on a fort\" (on-build fort (transfer actor treasury powder (/ (holding actor powder) 2))))"
    , "(law \"Half on a sloop\" (on-build sloop (transfer actor treasury rum (/ (holding actor rum) 2))))"
    , "(law \"Rum levy\" (on-round-end (for-each-player true (transfer each treasury rum (/ (holding each rum) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap sloops\" (set-cost sloop (bundle (timber 1))))"
    , "(law \"Roller's gift\" (on-roll (transfer bank actor rum 1)))"
    , "(law \"Sack on a 7\" (on-roll (for-each-player (and (= rolled 7) (< (points actor) (points each))) (move-piece each actor wharf))))"
    , "(law \"Lighthouses\" (new-piece lighthouse (bundle (powder 2) (timber 2)) (points 2) (attach wharf) (yield 1) (limit 2)))" ]
  else if spec.id == pitSpec.id then
    [ "(law \"Half on an elevator\" (on-build elevator (transfer actor treasury gold (/ (holding actor gold) 2))))"
    , "(law \"Rail toll\" (on-build rail (transfer actor treasury iron 1)))"
    , "(law \"Gold levy\" (on-round-end (for-each-player true (transfer each treasury gold (/ (holding each gold) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap rails\" (set-cost rail (bundle (lumber 1))))"
    , "(law \"Bid tax\" (on-round-end (for-each-player (< 0 (declared each gold)) (transfer each treasury gold 1))))"
    , "(law \"Panic on a 12\" (on-roll (for-each-player (= rolled 12) (transfer each bank wheat (holding each wheat)))))"
    , "(law \"Mills\" (new-piece mill (bundle (lumber 2) (gold 2)) (points 2) (attach farm) (yield 1) (limit 2)))" ]
  else if spec.id == omertaSpec.id then
    [ "(law \"Half on a club\" (on-build club (transfer actor treasury cash (/ (holding actor cash) 2))))"
    , "(law \"Half on a racket\" (on-build racket (transfer actor treasury wine (/ (holding actor wine) 2))))"
    , "(law \"Fish levy\" (on-round-end (for-each-player true (transfer each treasury fish (/ (holding each fish) 2)))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap streets\" (set-cost street (bundle (cement 1))))"
    , "(law \"Dirt on a 7\" (on-roll (for-each-player (= rolled 7) (transfer bank each dirt 1))))"
    , "(law \"Rats pay\" (on-round-end (for-each-player (= 0 (holding each dirt)) (transfer each treasury cash 1))))"
    , "(law \"Pizzerias\" (new-piece pizzeria (bundle (wine 2) (cement 2)) (points 2) (attach front) (yield 1) (limit 2)))" ]
  else
    [ "(law \"Half on a city\" (on-build city (transfer actor treasury grain (/ (holding actor grain) 2))))"
    , "(law \"Half on a road\" (on-build road (transfer actor treasury timber (/ (holding actor timber) 2))))"
    , "(law \"Half on a settlement\" (on-build settlement (transfer actor treasury grain (/ (holding actor grain) 2))))"
    , "(law \"Wool levy\" (on-round-end (for-each-player true (transfer each treasury wool (/ (holding each wool) 2)))))"
    , "(law \"Dole and tithe\" (on-round-end (for-each-player true (transfer bank each grain 1))) (on-harvest (if (< 1 (holding actor grain)) (transfer actor treasury grain 1))))"
    , "(law \"Tithe\" (on-harvest (transfer actor treasury res (/ amount 2))))"
    , "(law \"Cheap cities\" (set-cost city (bundle (grain 2) (ore 2))))"
    , "(law \"Roller's gift\" (on-roll (transfer bank actor grain 1)))"
    , "(law \"Half on a 7\" (on-roll (for-each-player (and (= rolled 7) (< 3 (+ (holding each grain) (holding each wool)))) (transfer each treasury grain (/ (holding each grain) 2)) (transfer each treasury wool (/ (holding each wool) 2)))))"
    , "(law \"Roll tithe\" (on-roll (for-each-player (<= 7 rolled) (transfer each treasury grain (/ (holding each grain) 2)))))"
    , "(law \"Lighthouses\" (new-piece lighthouse (bundle (ore 2) (brick 2)) (points 2) (attach settlement) (yield 1) (limit 2)))" ]

structure Tally where
  turnEnds : Nat := 0
  lastTurns : Nat := 0
  lastTurnsWithRoll : Nat := 0
  lawChangedRoll : Nat := 0
  builds : Nat := 0
  buildsChanged : Nat := 0
  /-- Builds where running the laws without posting the cost first would have given the wrong figures.
  This shows that the check can see that mistake. -/
  costFirstMatters : Nat := 0
  /-- Turn ends where a law that reacts to the roll changed what the engine did. -/
  rollLawChanged : Nat := 0
  /-- Of those, how many times running the roll law before the harvest posted would have given the wrong
  figures. This shows that the check can see that mistake. -/
  harvestFirstMatters : Nat := 0
  failures : List String := []

/-- Vote yes until the law passes. It returns the state just before the deciding vote, and after it. -/
def voteIn (s : State G) (id : Nat) : Option (State G × State G) := Id.run do
  let mut x := s
  for seat in s.turnOrder do
    match Engine.step G x (.vote seat id true) with
    | .error _ => return none
    | .ok y =>
      if (y.openProposal? id).isNone then
        if y.laws.any (·.1 == id) then return some (x, y) else return none
      x := y
  return none

/-- Try one law at one point in a game, and compare the preview with what the engine does. -/
def tryLaw (spec : GameSpec) (s : State spec.G) (seat : Nat) (text : String) (t : Tally) : Tally := Id.run do
  let G := spec.G
  let .ok (.law L) := Rules.parseProposal text (G.resources.map (·.name)) | return t
  let .ok s1 := Engine.step G s (.propose seat (.law L)) | return t
  let id := s1.nextProposalId - 1
  let some (before, passed) := voteIn s1 id | return t
  if passed.phase == .ended then return t
  let withLaw := before.withLaw id L
  let mut t := t
  -- Case 1: the turn ends now.
  match Engine.step G passed (.move seat .endTurn), Engine.step G before (.move seat .endTurn) with
  | .ok e1, .ok e0 =>
    let actual := actualRows before (newEntries passed e1) (newEntries before e0)
    let early := beforeRollRows before withLaw
    let rolled := e1.rollsMade != passed.rollsMade
    let shown := match rolled, e1.lastRoll with
      | true, some r => early ++ rollRows before withLaw r
      | _, _ => early
    let isRollLaw := L.clauses.any fun | .onRoll _ => true | _ => false
    let early' : List Entry := before.entriesBeforeRoll
    let wrongOrder : List Row := match rolled, e1.lastRoll, withLaw.nextRoller with
      | true, some r, some a =>
        -- Plan the roll law before the harvest posts, and put the harvest in front of it.
        let start := withLaw.afterPosting early'
        let wrong := harvestEntries start r ++ lawEntries start (.roll a r)
        early ++ rowsOf before (afterTheRoll before r) wrong
      | _, _, _ => early
    t := { t with
      rollLawChanged := t.rollLawChanged + (if isRollLaw && !actual.isEmpty then 1 else 0)
      harvestFirstMatters := t.harvestFirstMatters +
        (if isRollLaw && !actual.isEmpty && !sameRows actual wrongOrder then 1 else 0)
      turnEnds := t.turnEnds + 1
      lastTurns := t.lastTurns + (if before.isLastTurn then 1 else 0)
      lastTurnsWithRoll := t.lastTurnsWithRoll + (if before.isLastTurn && rolled then 1 else 0)
      lawChangedRoll := t.lawChangedRoll + (if actual.isEmpty then 0 else 1) }
    if !sameRows actual shown then
      let shownJson := (total shown).map rowJson
      let actualJson := (total actual).map rowJson
      t := { t with failures := s!"{L.title} at a turn's end, last turn {before.isLastTurn}: the preview said {(Json.arr shownJson.toArray).compress}, the engine did {(Json.arr actualJson.toArray).compress}" :: t.failures }
  | _, _ => pure ()
  -- Case 2: the seat builds. One place for each kind it can build, with the law and without it.
  let moves := (Engine.legalMoves G passed seat).filterMap fun | m@(.place k _) => some (k, m) | _ => none
  let oneEach := moves.foldl (fun (acc : List (PieceKind × Move)) x =>
    if acc.any (·.1 == x.1) then acc else acc ++ [x]) []
  for (k, m) in oneEach do
    match Engine.step G passed (.move seat m), Engine.step G before (.move seat m) with
    | .ok b1, .ok b0 =>
      -- A build that ends the game adds refunds, which commandment VII allows and a preview does not list.
      if b1.phase != .ended && b0.phase != .ended then
        let actual := actualRows before (newEntries passed b1) (newEntries before b0)
        let shown := if canPay withLaw seat k then buildRows before withLaw seat k else []
        let wrongWay := rowsOf before (before.costEntries seat k ++ lawEntries before (.build seat k))
          (withLaw.costEntries seat k ++ lawEntries withLaw (.build seat k))
        t := { t with
          builds := t.builds + 1
          buildsChanged := t.buildsChanged + (if actual.isEmpty then 0 else 1)
          costFirstMatters := t.costFirstMatters + (if sameRows actual wrongWay then 0 else 1) }
        if !sameRows actual shown then
          let shownJson := (total shown).map rowJson
          let actualJson := (total actual).map rowJson
          t := { t with failures := s!"{L.title} on building a {k}: the preview said {(Json.arr shownJson.toArray).compress}, the engine did {(Json.arr actualJson.toArray).compress}" :: t.failures }
    | _, _ => pure ()
  return t

/-- A table of seats, ready to start. -/
def newTable (spec : GameSpec) (seats seed : Nat) : Except String Game := do
  let g0 ← create (Json.mkObj [("t", "create"), ("code", "CHECK"), ("seats", toJson seats), ("game", spec.id),
    ("_serverSeed", toJson seed)])
  let g1 ← (List.range seats).foldlM (fun g i =>
    apply g (Json.mkObj [("t", "join"), ("name", s!"Bot {i}"), ("kind", "bot"), ("_token", s!"t{i}"), ("nonce", toJson (seed + i))])) g0
  apply g1 (Json.mkObj [("t", "start")])

/-- Play a game with the bots, or with seats that only end their turns so that it reaches its last
round, and try the laws along the way. -/
def playAndCheck (spec : GameSpec) (seats seed : Nat) (idle : Bool) (every : Nat) (t0 : Tally) : Tally := Id.run do
  let .ok g0 := newTable spec seats seed | return { t0 with failures := "a table did not start" :: t0.failures }
  let mut g := g0
  let mut t := t0
  let mut n := 0
  for _ in [0:4000] do
    let some s := g.state | break
    if s.phase == .ended then break
    if s.phase == .actions && s.openProposals.isEmpty && (n % every == 0 || s.isLastTurn) then
      if let some seat := s.currentSeat then
        for text in lawsFor spec do
          t := tryLaw g.spec s seat text t
    n := n + 1
    let next : Option Json :=
      if idle && s.phase == .actions then
        s.currentSeat.map fun p => Bots.moveEvent p .endTurn
      else Player.nextRuleEvent g
    let some ev := next | break
    match apply g ev with
    | .ok g' => g := g'
    | .error _ => break
  return t

/-- Check many games. Prints what it tried, so that a pass cannot be empty. -/
def run : IO Bool := do
  let mut t : Tally := {}
  for spec in gameSpecs do
    for seats in [2, 3, 4].filter (fun n => spec.minSeats ≤ n && n ≤ spec.maxSeats) do
      for seed in [1, 2] do
        t := playAndCheck spec seats (seed * 1000 + seats) false 2 t
      t := playAndCheck spec seats (7000 + seats) true 3 t
  IO.println s!"previews: {t.turnEnds} turn ends, {t.lawChangedRoll} changed by a law, {t.lastTurns} last turns, {t.lastTurnsWithRoll} of them with a roll; {t.builds} builds, {t.buildsChanged} changed by a law, {t.costFirstMatters} where the cost must be posted first; {t.rollLawChanged} turn ends changed by a law that reacts to the roll, {t.harvestFirstMatters} where the harvest must be posted first"
  let enough := t.turnEnds > 50 && t.lawChangedRoll > 10 && t.lastTurns > 10 && t.lastTurnsWithRoll > 5 &&
    t.lastTurns > t.lastTurnsWithRoll && t.builds > 20 && t.buildsChanged > 5 && t.costFirstMatters > 0 &&
    t.rollLawChanged > 10 && t.harvestFirstMatters > 0
  if !enough then IO.println "previews: FAILED: too few cases were tried for this to mean anything"
  for f in t.failures.reverse.take 15 do
    IO.println s!"previews: FAILED: {f}"
  return t.failures.isEmpty && enough

end CharterServer.PreviewCheck
