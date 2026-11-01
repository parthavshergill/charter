import Charter.Engine
import Charter.Games.Tiny

/-!
# Three complete games

The event lists of one full game each of Tiny Settlers, Tiny Space and Tiny Founded. The theorems
`a_full_game_exists`, `a_full_space_game_exists` and `a_founded_game_exists` run these games, and
`Charter/EngineTests.lean` tests them. This file imports only the engine and the two games, so a failing test cannot stop a
proof from building.
-/

namespace Charter.Games

open Charter Charter.Engine

/-! ## Helpers -/

def endT (p : Seat) : Event := .move p .endTurn
def placeAt (p : Seat) (k : PieceKind) (v : Nat) : Event := .move p (.place k (.spot v))
def placeOn (p : Seat) (k : PieceKind) (a b : Nat) : Event := .move p (.place k (.link (a, b)))

/-! ## Tiny Settlers -/

/-- The law in the full Tiny Settlers game: cities get cheaper. -/
def cheapCities : Law :=
  { title := "Cheap cities", clauses := [.setCost "city" [("grain", 2)]] }

/-- Tiny Settlers, a setup in which every seat places everything. -/
def settlersFullSetup : List Event :=
  [ placeAt 0 "settlement" 0, placeOn 0 "road" 0 1, endT 0
  , placeAt 1 "settlement" 2, placeOn 1 "road" 2 3, endT 1
  , placeAt 1 "settlement" 4, placeOn 1 "road" 4 5, endT 1
  , placeAt 0 "settlement" 7, placeOn 0 "road" 7 8, endT 0 ]

/-- The deal in the full Tiny Settlers game: seat 1 pays seat 0 one timber, with one more in deposit. -/
def timberForOneRound : Deal :=
  { title := "Timber for a round", signers := [1, 0], rounds := 1, exitNotice := 0
    deposits := [(1, "timber", 2)]
    terms := [.everyRound [{ src := 1, dst := .seat 0, res := "timber", amount := 1 }]] }

/-- Rolls in this game are 2, 2 / 1, 3 / 3, 1 / 3, 1. Seat 0 proposes cheaper cities in round 2 and
both seats vote yes. A deal runs in round 1. Seat 1 then upgrades both settlements and wins with 4 points in round 4. -/
def settlersGameEvents : List Event :=
  settlersFullSetup ++
  [ endT 0                                          -- round 1: rolls 2, 2
  , .propose 1 (.deal timberForOneRound)            -- seat 1 has timber, and both seats sign
  , .sign 0 0, .sign 1 0
  , endT 1                                          -- the deal pays once and refunds the rest
  , .propose 0 (.law cheapCities)                   -- round 2: roll 1 pays seat 0 the fee
  , .vote 0 1 true, .vote 1 1 true
  , endT 0, endT 1                                  -- rolls 1, 3
  , endT 0                                          -- round 3: roll 3
  , placeAt 1 "city" 2                              -- roll 1 gave seat 1 its second grain
  , endT 1
  , endT 0                                          -- round 4: roll 3
  , placeAt 1 "city" 4 ]                            -- roll 1: the city at spot 2 pays 2 grain

/-! ## Tiny Space -/

/-- Tiny Space, setup. Every seat places everything, on both rings of the map. -/
def spaceSetup : List Event :=
  [ placeAt 0 "outpost" 0, placeOn 0 "lane" 0 1, endT 0
  , placeAt 1 "outpost" 2, placeOn 1 "lane" 2 3, endT 1
  , placeAt 2 "outpost" 5, placeOn 2 "lane" 4 5, endT 2
  , placeAt 2 "outpost" 7, placeOn 2 "lane" 6 7, endT 2
  , placeAt 1 "outpost" 10, placeOn 1 "lane" 10 11, endT 1
  , placeAt 0 "outpost" 12, placeOn 0 "lane" 12 13, endT 0 ]

/-- The law in the full Tiny Space game: a station is worth 5 points, the target. -/
def stationsWin : Law :=
  { title := "Stations are capitals", clauses := [.setPoints "station" 5] }

/-- The deal in the full Tiny Space game: seat 0 pays seat 2 one alloy, with nothing left over. -/
def alloyForOneRound : Deal :=
  { title := "Alloy for a round", signers := [0, 2], rounds := 1, exitNotice := 0
    deposits := [(0, "alloy", 1)]
    terms := [.everyRound [{ src := 0, dst := .seat 2, res := "alloy", amount := 1 }]] }

/-- Rolls in this game are 3, 3, 4 / 3, 4, 2 / 2, 3, 2 / 2. Seat 1 has alloy for the fee in round 2.
Seats 0 and 2 vote yes, which is 2 of 3. Seat 0 reaches 4 helium at the start of round 4 and builds
a station, which wins. -/
def spaceGameEvents : List Event :=
  spaceSetup ++
  [ endT 0, endT 1, endT 2                 -- round 1: rolls 3, 3, 4
  , .propose 0 (.deal alloyForOneRound)    -- round 2: roll 3, and seat 0 has 1 alloy
  , .sign 0 0, .sign 2 0
  , endT 0
  , .propose 1 (.law stationsWin)          -- roll 4 gave seat 1 its second alloy
  , endT 1
  , .vote 0 1 true, .vote 2 1 true         -- roll 2, seat 2's turn
  , endT 2
  , endT 0, endT 1, endT 2                 -- round 3: rolls 2, 3, 2
  , placeAt 0 "station" 0 ]                -- round 4: roll 2 gave seat 0 its fourth helium

/-! ## Tiny Founded -/

/-- The Tiny Settlers game again, with cheap cities from the start. The founding law has id 0, so the
deal is proposal 1. Seat 1 still upgrades both settlements and wins in round 4. -/
def foundedGameEvents : List Event :=
  settlersFullSetup ++
  [ endT 0
  , .propose 1 (.deal timberForOneRound)
  , .sign 0 1, .sign 1 1
  , endT 1
  , endT 0, endT 1
  , endT 0
  , placeAt 1 "city" 2
  , endT 1
  , endT 0
  , placeAt 1 "city" 4 ]

/-! ## What the theorems claim -/

/-- The claims of `a_full_game_exists`, as a test. -/
def endedWithWinnerAndLaw {G : GameDef} (r : Except String (State G)) : Bool :=
  match r with
  | .ok s => s.phase == .ended && s.winner.isSome && !s.laws.isEmpty && decide (1 ≤ s.dealsStarted)
  | .error _ => false

/-- The claims of `a_founded_game_exists`, as a test. -/
def endedWithFoundingLaw {G : GameDef} (r : Except String (State G)) : Bool :=
  match r with
  | .ok s => s.phase == .ended && s.winner.isSome && s.laws.map (·.1) == [0]
  | .error _ => false

end Charter.Games
