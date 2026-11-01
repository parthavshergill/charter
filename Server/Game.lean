import Lean.Data.Json
import Lobby
import Charter.Constitution
import Charter.Scene.OfState
import Server.Util
import Server.Spec
import Server.Persona
import Server.Rules
import Server.Text
import Server.Preview

/-!
# One game, as a fold over its log

A game is its log of JSON events. `apply` adds one event. Table events (`create`, `join`, `start`)
go to `lean-lobby`. Every event that changes the game goes through `Engine.step`, and a rejected
event changes nothing. Replaying the log gives the same game again.

The game's definition is chosen when the table is created, and the first log entry names it. The live
state has type `Charter.Game G`, a state with proof that the engine reached it from a legal start. So
every theorem in `Charter/Constitution.lean` applies to what this server holds.
-/

namespace CharterServer.Game
open Lean Charter

variable {G : GameDef}

/-- One sentence of the chronicle. -/
structure Line where
  /-- The index of the event in the log. -/
  event : Nat
  /-- The seat that acted, if one did. -/
  actor : Option Nat
  text : String
  /-- The round it happened in. 0 is the founding. -/
  round : Nat := 0
  /-- What kind of event this is, for the screen: `build`, `law`, `deal`, `trade`, `roll`, `money`, `turn`, `end`. -/
  kind : String := "turn"
  /-- Worth telling. Routine lines are in the log, and hidden unless asked for. -/
  major : Bool := false

/-- How a law's vote ended, kept for the screen after the proposal leaves the open list. -/
structure Decision where
  id : Nat
  by_ : Nat
  law : Law
  votes : List (Nat × Bool)
  /-- `passed`, `failed` or `lapsed`. -/
  outcome : String
  round : Nat
  /-- The log index of the event that ended it. -/
  event : Nat

/-- One proposal put to the table, law or deal, kept for the clerk's memory. All of this is public:
the chronicle tells the same story. -/
structure Tabled where
  id : Nat
  by_ : Nat
  body : Proposal
  /-- The round it was proposed in. -/
  round : Nat
  /-- `open`, `passed`, `failed`, `lapsed` or `started`. -/
  outcome : String := "open"

structure Game where
  /-- The game this table plays. It never changes. -/
  spec : GameSpec
  room : Lobby.Room
  /-- `human`, `bot` or `claude`, by seat. -/
  kinds : Array String := #[]
  /-- The persona of each Claude seat, by seat. -/
  personas : Array (Option Persona.Persona) := #[]
  serverSeed : UInt64
  nonces : List UInt64 := []
  /-- The state of a started game, with proof that it is reachable. -/
  live : Option (Charter.Game spec.G) := none
  chronicle : Array Line := #[]
  /-- Every law that has left the open list, in order. -/
  decisions : Array Decision := #[]
  /-- Every proposal made, in order, with how it has ended so far. -/
  tabled : Array Tabled := #[]
  /-- The state when each open proposal was made, to tell when its preview has moved on. -/
  opened : List (Nat × State spec.G) := []
  /-- How many events are in the log. -/
  events : Nat := 0

instance : Inhabited Game := ⟨{ spec := default, room := default, serverSeed := 0 }⟩

/-- The state of a started game. -/
def Game.state (g : Game) : Option (State g.spec.G) := g.live.map (·.1)

/-- The names of this game's resources. -/
def Game.resources (g : Game) : List Res := g.spec.G.resources.map (·.name)

/-- Read the formal text of a law or a deal, for this game. -/
def Game.parse (g : Game) (text : String) : Except String Proposal :=
  Rules.parseProposal text g.resources

def Game.nameOf (g : Game) (seat : Nat) : String :=
  match g.room.seats[seat]? with
  | some (some i) => i.name
  | _ => s!"Seat {seat}"

def Game.isBot (g : Game) (seat : Nat) : Bool := g.kinds[seat]? == some "bot"

def Game.isClaude (g : Game) (seat : Nat) : Bool := g.kinds[seat]? == some "claude"

def Game.isHuman (g : Game) (seat : Nat) : Bool := g.kinds[seat]? == some "human"

def Game.botSeats (g : Game) : List Nat :=
  (List.range g.kinds.size).filter g.isBot

def Game.claudeSeats (g : Game) : List Nat :=
  (List.range g.kinds.size).filter g.isClaude

def Game.humanSeats (g : Game) : List Nat :=
  (List.range g.kinds.size).filter g.isHuman

/-- The game is over, or no person holds a seat. Then a spectator may read everything. -/
def Game.openToSpectators (g : Game) : Bool :=
  g.humanSeats.isEmpty || match g.state with
    | some s => s.phase == .ended
    | none => false

/-! ## JSON for moves and events -/

def bundleJson (b : Bundle) : Json :=
  Json.arr (b.map fun x => Json.mkObj [("res", x.1), ("n", toJson x.2)]).toArray

def bundleOfJson (j : Json) : Except String Bundle := do
  let items ← j.getArr?
  (items.toList.mapM fun i => do
    let r ← i.getObjValAs? String "res"
    let n ← i.getObjValAs? Nat "n"
    pure (r, n))

def moveJson : Move → Json
  | .place k (.spot v) => Json.mkObj [("t", "place"), ("kind", k), ("spot", toJson v)]
  | .place k (.link l) => Json.mkObj [("t", "place"), ("kind", k), ("link", toJson [l.1, l.2])]
  | .bankTrade give get => Json.mkObj [("t", "bankTrade"), ("give", give), ("get", get)]
  | .offer to give get =>
      Json.mkObj [("t", "offer"), ("to", toJson to), ("give", bundleJson give), ("get", bundleJson get)]
  | .accept id => Json.mkObj [("t", "accept"), ("id", toJson id)]
  | .cancel id => Json.mkObj [("t", "cancel"), ("id", toJson id)]
  | .endTurn => Json.mkObj [("t", "endTurn")]

def moveOfJson (j : Json) : Except String Move := do
  match ← j.getObjValAs? String "t" with
  | "place" =>
    let k ← j.getObjValAs? String "kind"
    match jNat j "spot", (j.getObjValAs? (List Nat) "link").toOption with
    | some v, _ => pure (.place k (.spot v))
    | none, some [a, b] => pure (.place k (.link (a, b)))
    | _, _ => throw "a place move needs a spot or a link"
  | "bankTrade" => pure (.bankTrade (← j.getObjValAs? String "give") (← j.getObjValAs? String "get"))
  | "offer" =>
    let to := jNat j "to"
    pure (.offer to (← bundleOfJson (← j.getObjVal? "give")) (← bundleOfJson (← j.getObjVal? "get")))
  | "accept" => pure (.accept (← j.getObjValAs? Nat "id"))
  | "cancel" => pure (.cancel (← j.getObjValAs? Nat "id"))
  | "endTurn" => pure .endTurn
  | t => throw s!"unknown move {t}"

/-- The engine event a log entry stands for. -/
def eventOfJson (g : Game) (j : Json) : Except String Event := do
  match ← j.getObjValAs? String "t" with
  | "move" => pure (.move (← j.getObjValAs? Nat "seat") (← moveOfJson (← j.getObjVal? "move")))
  | "propose" =>
    pure (.propose (← j.getObjValAs? Nat "seat") (← g.parse (← j.getObjValAs? String "text")))
  | "vote" =>
    pure (.vote (← j.getObjValAs? Nat "seat") (← j.getObjValAs? Nat "id") (← j.getObjValAs? Bool "yes"))
  | "sign" => pure (.sign (← j.getObjValAs? Nat "seat") (← j.getObjValAs? Nat "id"))
  | "exit" => pure (.exit (← j.getObjValAs? Nat "seat") (← j.getObjValAs? Nat "dealId"))
  | "forceEndTurn" => pure .forceEndTurn
  | t => throw s!"unknown event {t}"

/-! ## The chronicle -/

/-- What this game calls a seat's account. -/
def accountText (g : Game) : Account → String
  | .bank => "the bank"
  | .treasury => "the treasury"
  | .player p => g.nameOf p
  | .deposit k p => s!"{g.nameOf p}'s deposit in deal {k}"

/-- Add up entries that move the same thing between the same accounts. -/
def groupEntries (es : List Entry) : List Entry :=
  es.foldl (fun (acc : List Entry) e =>
    if acc.any (fun x => x.src == e.src && x.dst == e.dst && x.res == e.res && x.reason == e.reason) then
      acc.map fun x =>
        if x.src == e.src && x.dst == e.dst && x.res == e.res && x.reason == e.reason then
          { x with amount := x.amount + e.amount } else x
    else acc ++ [e]) []

/-- One entry as a sentence. Costs and trades are in the sentence about the move. -/
def entryLine (g : Game) (e : Entry) : Option (String × String × Bool) :=
  if e.amount == 0 then none else
  match e.reason with
  | .harvest => some ("money", s!"{accountText g e.dst} collected {e.amount} {e.res}.", false)
  | .lawEffect => some ("money", s!"By law, {accountText g e.src} paid {accountText g e.dst} {e.amount} {e.res}.", false)
  | .dealPayment => some ("money", s!"Under a deal, {accountText g e.dst} received {e.amount} {e.res} from {accountText g e.src}.", false)
  | .refund => some ("money", s!"{accountText g e.dst} got back {e.amount} {e.res} from a closed deal.", false)
  | .setDeposit => some ("money", s!"{accountText g e.src} set aside {e.amount} {e.res}.", false)
  | _ => none

def article (k : String) : String := Text.article k

/-- The empty board, for drawing the map before a game has started. It is not a game. -/
def emptyBoard (spec : GameSpec) : State spec.G := initialState spec.G minSeats 0 [0]

/-- The game's own link piece has this name. -/
def isLinkKind (G : GameDef) (k : String) : Bool := ((linkPiece G).map (·.name)) == some k

/-- The game's own spot piece has this name. -/
def isSpotKind (G : GameDef) (k : String) : Bool := ((spotPiece G).map (·.name)) == some k

/-- Told once in a game: the first of a kind of building in this world. -/
def firstOnIsland (g : Game) (s : State G) (k : String) : String :=
  if !isLinkKind G k && (s.pieces.filter (·.kind == k)).isEmpty then s!", the first on {g.spec.layout.word}" else ""

/-- The sentence for what the actor did: its kind, its text, and whether it is worth telling. -/
def actionText (g : Game) (s s' : State G) : Event → String × String × Bool
  | .move p (.place k _) =>
    if s.phase == .setup then
      if isLinkKind G k then ("build", s!"{g.nameOf p} laid {article k}.", false)
      else ("build", s!"{g.nameOf p} founded {article k}.", true)
    else
      match s.rules.piece? k with
      | some { placement := .upgrade old, .. } =>
        ("build", s!"{g.nameOf p} raised {article k} from a {old}{firstOnIsland g s k}.", true)
      | _ =>
        if isLinkKind G k then ("build", s!"{g.nameOf p} laid {article k}.", false)
        else if isSpotKind G k then ("build", s!"{g.nameOf p} founded {article k}.", true)
        else ("build", s!"{g.nameOf p} built {article k}{firstOnIsland g s k}.", true)
  | .move p (.bankTrade give get) =>
    ("trade", s!"{g.nameOf p} traded {s.rules.bankRate} {give} to the bank for 1 {get}.", false)
  | .move p (.offer to give get) =>
    let who := match to with
      | some q => s!" to {g.nameOf q}"
      | none => ""
    ("trade", s!"{g.nameOf p} offered {Text.bundleText give}{who}, asking for {Text.bundleText get}.", false)
  | .move p (.accept id) =>
    match s.offers.find? (·.id == id) with
    | some o =>
      ("trade", s!"{g.nameOf p} accepted {g.nameOf o.src}'s offer: {Text.bundleText o.give} for {Text.bundleText o.get}.", true)
    | none => ("trade", s!"{g.nameOf p} accepted an offer.", true)
  | .move p (.cancel _) => ("trade", s!"{g.nameOf p} took back an offer.", false)
  | .move p .endTurn => ("turn", s!"{g.nameOf p} ended their turn.", false)
  | .forceEndTurn =>
    match s.currentSeat with
    | some p => ("turn", s!"The timer ended {g.nameOf p}'s turn.", true)
    | none => ("turn", "The timer ended the turn.", true)
  | .propose p (.law L) => ("law", s!"{g.nameOf p} proposed \"{L.title}\".", true)
  | .propose p (.deal d) => ("deal", s!"{g.nameOf p} proposed a deal. {Text.dealLine g.nameOf d}", true)
  | .vote p id yes =>
    let word := if yes then "yes" else "no"
    let name := match (s.openProposal? id).map (·.body) with
      | some (.law L) => s!"\"{L.title}\""
      | _ => "a law"
    let base := s!"{g.nameOf p} voted {word} on {name}."
    if s'.laws.map (·.1) != s.laws.map (·.1) then ("law", s!"{base} The law passed.", true)
    else if (s'.openProposal? id).isNone then ("law", s!"{base} The law can no longer pass, so it failed.", true)
    else ("law", base, false)
  | .sign p id =>
    let whose := match (s.openProposal? id) with
      | some x => s!"{g.nameOf x.by_}'s deal"
      | none => "a deal"
    if s'.dealsStarted != s.dealsStarted then ("deal", s!"{g.nameOf p} signed {whose}. The deal started.", true)
    else ("deal", s!"{g.nameOf p} signed {whose}.", false)
  | .exit p _ => ("deal", s!"{g.nameOf p} gave notice on a deal.", true)

def actorOf : Event → Option Nat
  | .move p _ | .propose p _ | .vote p _ _ | .sign p _ | .exit p _ => some p
  | .forceEndTurn => none

/-- All the sentences for one accepted event. Each has its actor, kind, text and weight. -/
def sentences (g : Game) (s s' : State G) (e : Event) : List (Option Nat × String × String × Bool) :=
  let actor := actorOf e
  -- A counter is not money, so it gets no line of its own. A pack's note says what a roll means.
  let moneyLines := ((groupEntries (newEntries s s')).filter (!markRes G ·.res)).filterMap (entryLine g)
  let rolled :=
    if s'.rollsMade != s.rollsMade then
      match s'.currentSeat, s'.lastRoll with
      | some p, some r =>
        [(some p, "roll", s!"{g.nameOf p} rolled {r}.", false)] ++
          ((g.spec.rollNotes.filter (·.1 == r)).map fun n => ((none : Option Nat), "roll", n.2, true))
      | _, _ => []
    else []
  let roundLine :=
    if s'.round != s.round then [((none : Option Nat), "turn", s!"Round {s'.round} began.", false)] else []
  let expired := (s.openProposals.filter fun p =>
      (s'.openProposal? p.id).isNone && s'.rollsMade != s.rollsMade).map fun p =>
    let what := match p.body with
      | .law L => s!"\"{L.title}\" lapsed without a majority."
      | .deal _ => s!"{g.nameOf p.by_}'s deal lapsed unsigned."
    ((none : Option Nat), "law", what, true)
  let over :=
    match s.winner, s'.winner with
    | none, some w => [((none : Option Nat), "end", s!"The game ended. {g.nameOf w} won with {s'.pointsOf w} points.", true)]
    | _, _ => []
  let beforeRoll := moneyLines.map fun (k, t, m) => ((none : Option Nat), k, t, m)
  let (k, t, m) := actionText g s s' e
  [(actor, k, t, m)] ++ roundLine ++ expired ++ rolled ++ beforeRoll ++ over

/-- Laws that left the open list in this step, with how they ended. -/
def closedLaws (g : Game) (s s' : State G) (e : Event) : List Decision :=
  s.openProposals.filterMap fun p =>
    if (s'.openProposal? p.id).isSome then none else
    match p.body with
    | .deal _ => none
    | .law L =>
      let votes := match e with
        | .vote seat id yes => if id == p.id then p.votes ++ [(seat, yes)] else p.votes
        | _ => p.votes
      let passed := s'.laws.any (·.1 == p.id)
      let isVote := match e with
        | .vote _ id _ => id == p.id
        | _ => false
      let outcome := if passed then "passed" else if isVote then "failed" else "lapsed"
      some { id := p.id, by_ := p.by_, law := L, votes, outcome, round := s.round, event := g.events }

/-- The list of tabled proposals after one step: a new one joins, and any that left the open list
get their outcome. -/
def nextTabled (g : Game) (s s' : State G) (e : Event) : Array Tabled :=
  let added := match e, s'.openProposals.getLast? with
    | .propose seat _, some p =>
      g.tabled.push { id := p.id, by_ := seat, body := p.body, round := s.round }
    | _, _ => g.tabled
  added.map fun t =>
    if t.outcome != "open" || (s'.openProposal? t.id).isSome then t else
    let isThis := match e with
      | .vote _ id _ | .sign _ id => id == t.id
      | _ => false
    let outcome := match t.body with
      | .law _ =>
        if s'.laws.any (·.1 == t.id) then "passed" else if isThis then "failed" else "lapsed"
      | .deal _ => if isThis && s'.dealsStarted != s.dealsStarted then "started" else "lapsed"
    { t with outcome }

/-! ## Applying events -/

/-- Make a game from its first event. -/
def create (j : Json) : Except String Game := do
  let code ← j.getObjValAs? String "code"
  let seats ← j.getObjValAs? Nat "seats"
  if seats < minSeats || maxSeats < seats then throw s!"a table has {minSeats} to {maxSeats} seats"
  let seed ← j.getObjValAs? Nat "_serverSeed"
  let some spec := specOf? (jStr j "game") | throw s!"there is no game called {(jStr j "game").getD ""}"
  if seats < spec.minSeats || spec.maxSeats < seats then
    throw s!"{spec.name} has {spec.minSeats} to {spec.maxSeats} seats"
  pure { spec, room := Lobby.Room.new code spec.minSeats seats, serverSeed := UInt64.ofNat seed, events := 1 }

/-- Seat the players and start. -/
def start (g : Game) : Except String Game :=
  match g.room.start with
  | .error r => .error s!"the game cannot start: {repr r}"
  | .ok (room, _) =>
    if h : minSeats ≤ room.filled ∧ room.filled ≤ maxSeats ∧ g.nonces ≠ [] then
      let names := ", ".intercalate ((List.range room.filled).map g.nameOf)
      let founded := g.spec.G.foundingLaws.map fun L =>
        ({ event := g.events, actor := none, text := s!"In force from the founding: \"{L.title}\".", kind := "law", major := true } : Line)
      .ok { g with
        room := room
        live := some ⟨initialState g.spec.G room.filled g.serverSeed g.nonces, .start _ _ _ h.1 h.2.1 h.2.2⟩
        chronicle := (g.chronicle.push
          { event := g.events, actor := none, text := s!"The game began with {names}.", kind := "turn", major := true }) ++ founded.toArray }
    else
      .error s!"the game cannot start: it needs {minSeats} to {maxSeats} seats and at least one player's nonce"

/-- Apply one log entry. A rejected entry leaves the game as it was. -/
def apply (g : Game) (j : Json) : Except String Game := do
  let bump (x : Game) : Game := { x with events := x.events + 1 }
  match ← j.getObjValAs? String "t" with
  | "join" =>
    let name ← j.getObjValAs? String "name"
    let token ← j.getObjValAs? String "_token"
    let kind ← j.getObjValAs? String "kind"
    let nonce ← j.getObjValAs? Nat "nonce"
    match g.room.join name token with
    | .error r => throw s!"cannot join: {repr r}"
    | .ok (room, _) =>
      pure (bump { g with
        room := room
        kinds := g.kinds.push kind
        personas := g.personas.push ((jField j "_persona").bind Persona.ofJson?)
        nonces := g.nonces ++ [UInt64.ofNat nonce] })
  | "start" => bump <$> start g
  | _ =>
    let some live := g.live | throw "the game has not started"
    let s := live.1
    let e ← eventOfJson g j
    match h : Engine.step g.spec.G s e with
    | .error err => throw err
    | .ok s' =>
      let lineRound := if s.phase == .setup then 0 else s.round
      let lines := (sentences g s s' e).map fun (actor, kind, text, major) =>
        { event := g.events, actor, text, kind, major, round := lineRound : Line }
      let opened := match e with
        | .propose .. => (s'.openProposals.getLast?.map (fun p => (p.id, s'))).toList ++ g.opened
        | _ => g.opened.filter fun x => (s'.openProposal? x.1).isSome
      pure (bump { g with
        live := some ⟨s', .next e live.2 h⟩
        chronicle := g.chronicle ++ lines.toArray
        decisions := g.decisions ++ (closedLaws g s s' e).toArray
        tabled := nextTabled g s s' e
        opened := opened })

end CharterServer.Game
