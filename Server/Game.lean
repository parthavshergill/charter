import Lean.Data.Json
import Lobby
import Charter.Constitution
import Charter.Scene.OfState
import Server.Util
import Server.MoveJson
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

/-! ## JSON for events -/

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
  let told := s!" {k}, the first on {g.spec.layout.word}"
  let toldBefore := g.chronicle.any fun l => (l.text.splitOn told).length > 1
  if !isLinkKind G k && (s.pieces.filter (·.kind == k)).isEmpty && !toldBefore then s!", the first on {g.spec.layout.word}" else ""

/-- This vote closes a law that passes `lawProblems`, so it passed. A law of only `now` clauses does not join
the laws in force, so the list of laws cannot say this. -/
def passedAtVote (s : State G) (id : Nat) : Bool :=
  match s.openProposal? id with
  | some { body := .law L, .. } => (lawProblems G s L).isEmpty
  | _ => false

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
  | .move p (.declare r n) => ("trade", s!"{g.nameOf p} declared {n} {r}.", true)
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
    else if (s'.openProposal? id).isNone && passedAtVote s id then ("law", s!"{base} The law passed and acted once. It does not stay in force.", true)
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

/-- The entries that laws made in reaction to the roll itself. They come last in a roll, so this is
what `rollEntries` holds after the harvest. -/
def rollLawPart (s : State G) (roll : Nat) : List Entry :=
  let x := s.afterRoundEnd
  (rollEntries x roll).drop (harvestEntries x.atRoll roll).length

/-- A law's title in a line, cut so that the line stays short. -/
def shortTitle (title : String) : String :=
  if title.length ≤ 40 then title else String.ofList (title.toList.take 39) ++ "…"

/-- How a line opens: `By law "Toll"`, or `By law "Toll" and "Tithe"`. Past two, it counts the rest. With no
title it is only `By law`. -/
def byLaw (titles : List String) : String :=
  let names := titles.eraseDups.map fun t => s!"\"{shortTitle t}\""
  let shown := if names.length ≤ 2 then names else names.take 2 ++ [s!"{names.length - 2} more"]
  if shown.isEmpty then "By law" else s!"By law {Text.andList shown}"

/-- The titles of the laws in force whose plan asks for a payment that was really made. A payment that
shrank to nothing was not made, so a law left with no payments is not named. -/
def actingTitles (s : State G) (planOf : Law → List Entry) (made : List Entry) : List String :=
  (s.laws.filter fun x => (planOf x.2).any fun e =>
    made.any fun m => m.src == e.src && m.dst == e.dst && m.res == e.res).map (·.2.title)

/-- What a law asks for in reaction to the bank's payments on this roll. The same plan as `harvestEntries`. -/
def harvestPlan (x : State G) (roll : Nat) (L : Law) : List Entry :=
  let base := baseHarvest x roll
  let after := x.afterPosting base
  base.flatMap fun e =>
    match e.dst with
    | .player p => Law.plan after (.harvest p e.res e.amount) L
    | _ => []

/-- What a law asks for in reaction to the roll itself. The same plan as `rollEntries`. -/
def rollPlan (x : State G) (roll : Nat) (L : Law) : List Entry :=
  match x.nextRoller with
  | some a => Law.plan (x.atRoll.afterPosting (harvestEntries x.atRoll roll)) (.roll a roll) L
  | none => []

/-- What the laws did at one moment, as one line: "By law "Seven tax", on a 7, Ada paid the bank 2 brick and
1 ore. Mara paid the bank 1 ore." A law can touch every seat at once, so the screen tells it in one caption.
`moment` is how the line says when, and it can be empty. -/
def lawSentence (g : Game) (titles : List String) (moment : String) (part : List Entry) : Option String :=
  let grouped := groupEntries part
  let pairs := grouped.foldl (fun (acc : List (Account × Account)) e =>
    if acc.contains (e.src, e.dst) then acc else acc ++ [(e.src, e.dst)]) []
  let words := pairs.map fun (a, b) =>
    let goods := (grouped.filter fun e => e.src == a && e.dst == b).map fun e => (e.res, e.amount)
    s!"{accountText g a} paid {accountText g b} {Text.bundleText goods}"
  match words with
  | [] => none
  | first :: rest =>
    let others := rest.map fun w => s!" {Text.capFirst w}."
    some s!"{byLaw titles}, {moment}{first}.{String.join others}"

def rollLawSentence (g : Game) (titles : List String) (roll : Nat) (part : List Entry) : Option String :=
  lawSentence g titles s!"on {Text.rollName roll}, " part

/-- What changed between two lists of pieces, seat by seat: "Ada lost a settlement and a mill", "Ben seized
Cleo's road". -/
def pieceSayings (g : Game) (seats : List Nat) (before after : List Piece) : List String :=
  let kindsText (taken : List PieceKind) : List String :=
    taken.eraseDups.map fun k =>
      let n := (taken.filter (· == k)).length
      if n == 1 then Text.article k else Text.plural n k
  seats.flatMap fun p =>
    let gone := before.filter fun x => x.owner == p && !after.contains x
    let goesTo (x : Piece) : Option Nat :=
      (after.find? fun y => y.loc == x.loc && y.kind == x.kind).map (·.owner)
    let lost := (gone.filter fun x => (goesTo x).isNone).map (·.kind)
    let takers := (gone.filterMap goesTo).eraseDups
    (if lost.isEmpty then [] else [s!"{g.nameOf p} lost {Text.andList (kindsText lost)}"]) ++
      takers.map fun q =>
        let seized := (gone.filter fun x => goesTo x == some q).map (·.kind)
        s!"{g.nameOf q} seized {Text.andList (seized.eraseDups.map fun k =>
          let n := (seized.filter (· == k)).length
          if n == 1 then s!"{g.nameOf p}'s {k}" else s!"{Text.plural n k} of {g.nameOf p}'s")}"

/-- One law's piece orders on one trigger, in the order `lawOrders` makes them. -/
def titledOrders (x : State G) (t : Trigger) : List (String × PieceOrder) :=
  x.laws.flatMap fun l =>
    (l.2.clauses.flatMap fun c => Effect.planOrdersAll x (c.bodyFor t) t.env).map (l.2.title, ·)

/-- Part of what the laws did to the pieces: one law's title, and the pieces before and after. -/
structure PieceStep where
  title : String
  before : List Piece
  after : List Piece

/-- Carry out these orders and keep the steps. One law's orders join into one step, so the line can say "2
settlements". They do not join when an order moves a piece the step just gave someone, so a piece that
moves twice shows both moves. -/
def pieceSteps (R : Rules) (start : List Piece) (orders : List (String × PieceOrder)) : List PieceStep :=
  (orders.foldl (fun (acc : List Piece × List PieceStep) (title, o) =>
    let (now, steps) := acc
    let next := applyOrder R now o
    if next == now then acc else
    let moved := now.filter (!next.contains ·)
    match steps.reverse with
    | last :: earlier =>
      let gained := last.after.filter (!last.before.contains ·)
      if last.title == title && !moved.any gained.contains then
        (next, (({ last with after := next } : PieceStep) :: earlier).reverse)
      else (next, steps ++ [{ title, before := now, after := next }])
    | [] => (next, [{ title, before := now, after := next }])) (start, [])).2

/-- What the laws did to the pieces in this step, in the order they did it. -/
def stepsOf (s : State G) (roll : Option Nat) (e : Event) : List PieceStep :=
  match e with
  | .vote _ id _ =>
    match s.openProposal? id with
    | some { body := .law L, .. } =>
      pieceSteps s.rules s.pieces (L.clauses.flatMap fun c =>
        (Effect.planOrdersAll s (c.bodyFor .now) Trigger.now.env).map (L.title, ·))
    | _ => []
  | .move _ .endTurn | .forceEndTurn =>
    let atEnd := if s.isLastTurn then
      pieceSteps s.rules s.pieces (titledOrders (s.afterPosting s.duePayments) .roundEnd) else []
    let x := s.afterRoundEnd
    let atRoll := match roll, x.nextRoller with
      | some r, some a =>
        pieceSteps x.rules x.pieces (titledOrders (x.atRoll.afterPosting (harvestEntries x.atRoll r)) (.roll a r))
      | _, _ => []
    atEnd ++ atRoll
  | _ => []

/-- An opening and some sentences, as one piece of text. -/
def sayWith (opening : String) (words : List String) : Option String :=
  match words with
  | [] => none
  | first :: rest => some s!"{opening}{first}.{String.join (rest.map fun w => s!" {w}.")}"

/-- What the laws did to the pieces at one moment, as one line: "By law "Sevens", Ada lost a settlement and a
mill. Ben seized Cleo's road." It names the law, and shows each move of a piece that moved twice. A law
can touch every seat at once, so the screen tells it in one caption. If the steps do not end where the
game did, it says only the result. -/
def pieceSentence (g : Game) (s s' : State G) (roll : Option Nat) (e : Event) : Option String :=
  let steps := stepsOf s roll e
  if steps.getLast?.map (·.after) != some s'.pieces then
    sayWith "By law, " (pieceSayings g s.turnOrder s.pieces s'.pieces)
  else
    let parts := (steps.foldl (fun (acc : Option String × List String) step =>
      let opening := if acc.1 == some step.title then "Then " else s!"{byLaw [step.title]}, "
      (some step.title, acc.2 ++ (sayWith opening (pieceSayings g s.turnOrder step.before step.after)).toList))
      (none, [])).2
    if parts.isEmpty then none else some (" ".intercalate parts)

/-- The deals that ended in this step, each as a line. A deal ends with its rounds, after a signer's notice,
or with the game. The chronicle tells a deal by who signed it. Its title is only someone's words. -/
def dealsEnded (g : Game) (s s' : State G) : List String :=
  (s.deals.filter fun d => !s'.deals.any (·.id == d.id)).map fun d =>
    s!"The deal between {Text.andList (d.deal.signers.map g.nameOf)} ended."

/-- The resources this roll owed someone, where the bank paid none of it. -/
def bankShort (x : State G) (roll : Nat) : List Res :=
  let owed := (G.map.regions.filter (·.number == roll)).flatMap fun region =>
    x.pieces.filterMap fun p =>
      match p.loc with
      | .spot v =>
        let n := ((x.rules.piece? p.kind).map (·.yield)).getD 0
        if n != 0 && region.spots.contains v then some region.res else none
      | .link _ => none
  let paid := (baseHarvest x roll).map (·.res)
  owed.eraseDups.filter (!paid.contains ·)

/-- The line for a roll the bank could not pay: "On a 6, the bank had no ore to pay anyone." The bank can
hold a little and still pay nothing, when each share rounds down to nothing. -/
def bankShortLine (x : State G) (roll : Nat) : Option String :=
  match bankShort x roll with
  | [] => none
  | short =>
    let words := short.map fun r => if x.balance .bank r == 0 then s!"no {r}" else s!"too little {r}"
    some s!"On {Text.rollName roll}, the bank had {Text.andList words} to pay anyone."

/-- All the sentences for one accepted event. Each has its actor, kind, text and weight. -/
def sentences (g : Game) (s s' : State G) (e : Event) : List (Option Nat × String × String × Bool) :=
  let actor := actorOf e
  let rollLaw := match s'.lastRoll with
    | some r => if s'.rollsMade != s.rollsMade then some (r, rollLawPart s r) else none
    | none => none
  let all := newEntries s s'
  let others := all.take (all.length - ((rollLaw.map (·.2.length)).getD 0))
  -- A counter is not money, so it gets no line of its own.
  let isLaw (x : Entry) : Bool := x.reason == .lawEffect && !markRes G x.res
  -- A law's payments are one line that the screen tells, and the other money has a line each.
  let moneyLines := ((groupEntries (others.filter (·.reason != .lawEffect))).filter (!markRes G ·.res)).filterMap (entryLine g)
  let isVote := match e with | .vote .. => true | _ => false
  let endsTurn := match e with
    | .move _ .endTurn | .forceEndTurn => true
    | _ => false
  let atRoundEnd := if endsTurn then s.entriesBeforeRoll.length else 0
  let afterEnd := s.afterRoundEnd
  let thisRoll := if s'.rollsMade != s.rollsMade then s'.lastRoll else none
  -- Which laws these payments came from, for each moment that has any.
  let otherPlan (L : Law) : List Entry := match e, thisRoll with
    | .move p (.place k _), _ => Law.plan (s.afterPosting (s.costEntries p k)) (.build p k) L
    | _, some r => harvestPlan afterEnd.atRoll r L
    | _, none => []
  let lawLine (titles : List Entry → List String) (moment : String) (part : List Entry) : List (Option Nat × String × String × Bool) :=
    let told := part.filter isLaw
    match lawSentence g (titles told) moment told with
    | some text => [((none : Option Nat), "money", text, true)]
    | none => []
  let roundEndLaw := lawLine
    (actingTitles s (Law.plan (s.afterPosting s.duePayments) .roundEnd)) "at the round's end, " (others.take atRoundEnd)
  let voted : List String := match e with
    | .vote _ id _ =>
      match s.openProposal? id with
      | some { body := .law L, .. } => [L.title]
      | _ => []
    | _ => []
  let otherLaw := lawLine (if isVote then fun _ => voted else actingTitles s otherPlan)
    (if isVote then "the moment it passed, " else if s'.rollsMade != s.rollsMade then "at the harvest, " else "") (others.drop atRoundEnd)
  let rollLawLine := match rollLaw with
    | some (r, part) =>
      let told := part.filter (!markRes G ·.res)
      match rollLawSentence g (actingTitles s (rollPlan afterEnd r) told) r told with
      | some text => [((none : Option Nat), "money", text, true)]
      | none => []
    | none => []
  let shortLine := match thisRoll with
    | some r =>
      match bankShortLine afterEnd.atRoll r with
      | some text => [((none : Option Nat), "roll", text, true)]
      | none => []
    | none => []
  let endedLines := (dealsEnded g s s').map fun text => ((none : Option Nat), "deal", text, true)
  let rolled :=
    if s'.rollsMade != s.rollsMade then
      match s'.currentSeat, s'.lastRoll with
      | some p, some r =>
        [(some p, "roll", s!"{g.nameOf p} rolled {r}.", false)]
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
    | none, some w =>
      let held := s'.tokenPointsOf w
      let from_ := if held == 0 then "" else s!", {held} of them from what they held"
      let how := if s'.lawEnds then "The game ended by law." else "The game ended."
      [((none : Option Nat), "end", s!"{how} {g.nameOf w} won with {s'.pointsOf w} points{from_}.", true)]
    | _, _ => []
  let beforeRoll := moneyLines.map fun (k, t, m) => ((none : Option Nat), k, t, m)
  -- A law can take a piece at a turn change. Tell it, or the board would change with no word.
  let pieceLines : List (Option Nat × String × String × Bool) :=
    if (match e with | .move _ (.place ..) => true | _ => false) then [] else
    match pieceSentence g s s' thisRoll e with
    | some text => [(none, "build", text, true)]
    | none => []
  let (k, t, m) := actionText g s s' e
  [(actor, k, t, m)] ++ roundEndLaw ++ endedLines ++ roundLine ++ expired ++ rolled ++ shortLine ++ beforeRoll ++ otherLaw ++ rollLawLine ++ pieceLines ++ over

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
      let isVote := match e with
        | .vote _ id _ => id == p.id
        | _ => false
      let passed := s'.laws.any (·.1 == p.id) || (isVote && (lawProblems G s L).isEmpty && L.isDecree)
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
      | .law L =>
        if s'.laws.any (·.1 == t.id) || (isThis && L.isDecree && (lawProblems G s L).isEmpty) then "passed"
        else if isThis then "failed" else "lapsed"
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
  -- Only the training harness's saved games name a dealt map. See `GameSpec.dealt`.
  let spec ← match j.getObjVal? "_map" with
    | .error _ => pure spec
    | .ok m =>
      let deal ← (fromJson? m : Except String (List (String × Nat)))
      match spec.dealt deal with
      | some d => pure d
      | none => throw s!"this map does not fit {spec.name}"
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
