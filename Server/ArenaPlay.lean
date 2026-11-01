import Server.BotCore

/-!
# One headless game

The arena's game loop. Every event goes through `Engine.step`, from the same start as `Game.start`, and
there is no log, no chronicle and no JSON in the loop.

Two things keep a long game fast, and neither changes what any rule sees:

* `State.journal` is emptied after each step. The engine only ever appends to it.
* `State.books` is a function that grows by one layer per entry posted, so a lookup walks every entry so
  far. `compact` replaces it with a table that gives the same answer for every account and resource.

`charter-arena --check-reference` and `--check-fixture` check that the loop chooses as the plain way does.
-/

namespace CharterServer.Arena
open Charter CharterServer.Bots

variable {G : GameDef}

/-- A number fixed by a game's seed and an index. `charter-sim` makes a table's seeds the same way. -/
def derive (seed : Nat) (i : Nat) : Nat :=
  (scramble (UInt64.ofNat seed + UInt64.ofNat i * 0x9E3779B97F4A7C15)).toNat

/-- The state a game starts from, for this seed: `charter-sim`'s table with this seed has the same one. -/
def startOf (G : GameDef) (seats seed : Nat) : State G :=
  initialState G seats (UInt64.ofNat (derive seed 0))
    ((List.range seats).map fun i => UInt64.ofNat (derive seed (200 + i)))

/-- The same books as a table. An account or resource the table does not cover goes to the old books. -/
def compact (names : Array String) (seats : Nat) (s : State G) : State G :=
  let old := s.books
  let nres := names.size
  let accounts := Account.bank :: Account.treasury :: (List.range seats).map Account.player
  let table : Array Nat := accounts.foldl (fun t a => names.foldl (fun t r => t.push (old a r)) t)
    (Array.mkEmpty ((seats + 2) * nres))
  let rec resIdx (r : String) (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if names.getD i "" == r then some i else resIdx r (i + 1) fuel
  { s with
    books := fun a r =>
      let row : Option Nat := match a with
        | .bank => some 0
        | .treasury => some 1
        | .player p => if p < seats then some (p + 2) else none
        | .deposit _ _ => none
      match row, resIdx r 0 nres with
      | some i, some j => table.getD (i * nres + j) 0
      | _, _ => old a r }

/-- How the loop runs. Both only change speed. -/
structure Options where
  /-- Remake the books after this many entries. 0 never does. -/
  compactEvery : Nat := 1
  /-- Empty the journal after each step. -/
  dropJournal : Bool := true
  deriving Inhabited

/-- One game in progress. -/
structure Play (G : GameDef) where
  state : State G
  events : Nat := 0
  rejected : Nat := 0
  offersMade : Array Nat
  offersAccepted : Array Nat
  /-- Entries posted since the books were last remade. -/
  posted : Nat := 0
  /-- The turn that `turnOffer` belongs to. -/
  turn : Nat := 0
  /-- The next offer id when this turn began. -/
  turnOffer : Nat := 0

/-- A game about to begin. -/
def Play.start (s : State G) (seats : Nat) : Play G :=
  { state := s, offersMade := Array.replicate seats 0, offersAccepted := Array.replicate seats 0 }

/-- What each seat plays. -/
structure Table (G : GameDef) where
  plans : Array (Strategy × Ctx G)
  /-- The resource names, for `compact`. -/
  names : Array String
  deriving Inhabited

/-- The events a table wants now, best first. Seats speak only if it is their turn, or if there is a
proposal or an offer to answer. A seat speaks only for itself: anything else it asks for is dropped, so a
strategy cannot vote for another seat, end its turn, or send the timer's event. -/
def wanted (t : Table G) (p : Play G) : List Event :=
  let s := p.state
  let ask (seat : Nat) : List Event :=
    match t.plans[seat]? with
    | none => []
    | some (st, ctx) =>
      let made := s.nextOfferId - p.turnOffer
      let ctx := if made == 0 || s.currentSeat != some seat then ctx else { ctx with offersThisTurn := made }
      (st.decide ctx s [seat]).filter (seatOf · == some seat)
  if s.openProposals.isEmpty && s.offers.isEmpty then
    match s.currentSeat with
    | some seat => ask seat
    | none => []
  else
    merged (s.turnOrder.map ask)

/-- The first of these events the engine accepts, and the state after it. -/
def firstAccepted (s : State G) : List Event → Option (Event × State G)
  | [] => none
  | e :: es =>
    match Engine.step G s e with
    | .ok s' => some (e, s')
    | .error _ => firstAccepted s es

/-- A game that threw away its turn: end the turn, or have the timer end it. -/
def endForcibly (s : State G) : Option (Event × State G) :=
  let endIt : List Event := match s.currentSeat with
    | some seat => [.move seat .endTurn]
    | none => []
  firstAccepted s (endIt ++ [.forceEndTurn])

/-- Count an accepted event in a game's numbers. -/
def Play.note (p : Play G) (e : Event) : Play G :=
  match e with
  | .move q (.offer ..) => { p with offersMade := p.offersMade.modify q (· + 1) }
  | .move _ (.accept id) =>
    match p.state.offers.find? (·.id == id) with
    | some o => { p with offersAccepted := p.offersAccepted.modify o.src (· + 1) }
    | none => p
  | _ => p

/-- One step of a game: the chosen event and the game after it. `none` means nothing can happen. -/
def advance (o : Options) (t : Table G) (p : Play G) : Option (Event × Play G) :=
  let s := p.state
  let p := if s.turnsTaken == p.turn then p else { p with turn := s.turnsTaken, turnOffer := s.nextOfferId }
  let (chosen, thrown) := match firstAccepted s (wanted t p) with
    | some x => (some x, false)
    | none => (endForcibly s, true)
  match chosen with
  | none => none
  | some (e, s') =>
    let p := p.note e
    let added := s'.journal.length - s.journal.length
    let s' := if o.dropJournal then { s' with journal := [] } else s'
    let posted := p.posted + added
    let again := o.compactEvery != 0 && posted ≥ o.compactEvery
    let s' := if again then compact t.names t.plans.size s' else s'
    some (e, { p with
      state := s'
      events := p.events + 1
      rejected := if thrown then p.rejected + 1 else p.rejected
      posted := if again then 0 else posted })

/-- Play on until the game ends, or for this many more events. -/
def run (o : Options) (t : Table G) : Nat → Play G → Play G
  | 0, p => p
  | fuel + 1, p =>
    if p.state.phase == .ended then p else
    match advance o t p with
    | none => p
    | some (_, p') => run o t fuel p'

/-- Most events a game can have, by the rules: a game that gets here is stuck. -/
def eventCap (G : GameDef) (seats : Nat) : Nat := maxEvents G seats + 1

/-- Play a whole game. -/
def playGame (o : Options) (t : Table G) (seed : Nat) : Play G :=
  let seats := t.plans.size
  run o t (eventCap G seats) (Play.start (startOf G seats seed) seats)

end CharterServer.Arena
