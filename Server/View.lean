import Server.Game
import Server.Formalize
import Server.Describe

/-!
# What a seat sees, as JSON

Lean decides everything here. The screen shows these fields and sends back moves from `legalMoves`.
Whether a seat can vote, sign or give notice comes from asking `Engine.step`.
-/

namespace CharterServer.View
open Lean Charter CharterServer.Game

variable {G : GameDef}

def phaseText : Phase → String
  | .setup => "setup"
  | .actions => "actions"
  | .ended => "ended"

def accepted (s : State G) (e : Event) : Bool := (Engine.step G s e).toOption.isSome

def locJson : Loc → List (String × Json)
  | .spot v => [("spot", toJson v)]
  | .link l => [("link", toJson [l.1, l.2])]

def locOfMove : Move → Option Loc
  | .place _ l => some l
  | _ => none

/-- The board's fixed shape. Positions are for the 2D fallback and are not in the spec. -/
def boardJson (spec : GameSpec) : Json :=
  let L := spec.layout
  Json.mkObj
    [ ("tiles", Json.arr (L.tiles.map fun t =>
        let (x, y) := t.hex.toPixel 1.0
        Json.mkObj [("x", toJson x), ("y", toJson y), ("res", toJson t.res), ("number", toJson t.number),
          ("pips", toJson ((t.number.map (Scene.chanceOf spec.G)).getD 0))]).toArray)
    , ("spots", Json.arr (L.spots.map fun v =>
        let (x, y) := v.toPixel 1.0
        Json.mkObj [("x", toJson x), ("y", toJson y)]).toArray)
    , ("links", Json.arr (L.links.map fun l => toJson [l.1, l.2]).toArray) ]

def pieceJson (x : Piece) : Json :=
  Json.mkObj ([("owner", toJson x.owner), ("kind", x.kind)] ++ locJson x.loc)

def handJson (s : State G) (a : Account) : Json :=
  Json.mkObj (G.resources.map fun r => (r.name, toJson (s.balance a r.name)))

def seatJson (g : Game) (s : Option (State g.spec.G)) (showPersona : Bool) (i : Nat) : Json :=
  let persona : List (String × Json) :=
    match showPersona, g.personas[i]? with
    | true, some (some p) => [("persona", p.styleOf.label), ("voice", p.voice)]
    | _, _ => []
  let base := [("seat", toJson i), ("name", toJson (g.nameOf i)), ("kind", toJson (g.kinds[i]?.getD "human"))] ++ persona
  match s with
  | none => Json.mkObj base
  | some st =>
    Json.mkObj (base ++
      [ ("points", toJson (st.pointsOf i))
      , ("hand", handJson st (.player i))
      , ("pieces", Json.mkObj (st.rules.pieces.map fun d => (d.name, toJson (st.countOf i d.name)))) ])

def placementName : Placement → String
  | .link => "link"
  | .spot => "spot"
  | .upgrade _ => "upgrade"
  | .attach _ => "attach"

/-- What is missing from a seat's hand to pay this bundle. Empty means it can pay. -/
def shortOf (s : State G) (p : Nat) (b : Bundle) : Bundle :=
  b.filterMap fun x =>
    let have_ := s.balance (.player p) x.1
    if have_ < x.2 then some (x.1, x.2 - have_) else none

def pieceDefJson (s : State G) (you : Option Nat) (legal : List Move) (d : PieceDef) : Json :=
  let spots := (legal.filter fun | .place k _ => k == d.name | _ => false).length
  let owned := match you with
    | some y => s.countOf y d.name
    | none => 0
  Json.mkObj
    [ ("name", d.name), ("cost", bundleJson d.cost), ("points", toJson d.points)
    , ("limit", toJson d.limit), ("yield", toJson d.yield), ("placement", placementName d.placement)
    , ("spots", toJson spots), ("owned", toJson owned)
    , ("short", bundleJson (match you with
        | some y => shortOf s y d.cost
        | none => []))
    , ("made", toJson (!(G.pieces.any (·.name == d.name)))) ]

/-- What a corner pays: the hexes it touches, likeliest first in the order of the map. -/
def yieldsOf (G : GameDef) (v : Nat) : Json :=
  Json.arr (((paidRegions G).filter (·.spots.contains v)).map fun r =>
    Json.mkObj [("res", r.res), ("number", toJson r.number),
      ("pips", toJson (Scene.chanceOf G r.number))]).toArray

def moveEntry (L : Scene.Layout) (s : State G) (m : Move) : Json :=
  let base : List (String × Json) :=
    [ ("move", moveJson m), ("label", Text.moveLabel s.rules.bankRate m)
    , ("pick", toJson ((Scene.pickOf L m).map (·.toNat))) ]
  match m with
  | .place k loc =>
    let cost := if s.phase == .setup then [] else s.costOf k
    let ys := match loc with
      | .spot v => [("yields", yieldsOf G v)]
      | .link _ => []
    Json.mkObj (base ++ [("kind", toJson k), ("cost", bundleJson cost)] ++ ys)
  | _ => Json.mkObj base

/-- The next thing this seat should do, in a few words. The screen shows only this. -/
def promptOf (g : Game) (s : State G) (you : Option Nat) (legal : List Move) : Json :=
  match you, s.currentSeat with
  | some y, some t =>
    if s.phase == .ended then Json.null
    else if y != t then Json.null
    else if s.phase == .setup then
      match legal.find? (fun | .place _ _ => true | _ => false) with
      | some (.place k _) => toJson s!"Place {Text.article k}. It is free."
      | _ =>
        let next := s.turnOrder[(if s.turnsTaken + 1 < s.turnOrder.length then s.turnsTaken + 1 else 0)]?
        let _ := next
        toJson "Placed. Press End turn."
    else
      let canBuild := legal.any fun | .place _ _ => true | _ => false
      toJson (if canBuild then "Your turn. Build, trade or end your turn." else "Your turn. Trade, propose a rule or end your turn.")
  | _, _ =>
    let _ := g
    Json.null

def feeJson {G : GameDef} (s : State G) (you : Option Nat) : Json :=
  let short := match you with
    | some y => shortOf s y G.lawFee
    | none => []
  Json.mkObj
    [ ("cost", bundleJson G.lawFee), ("short", bundleJson short)
    , ("canPay", toJson short.isEmpty) ]

/-- A law's preview for this viewer, and whether it has moved on since the law was proposed. -/
def previewFor (g : Game) (s : State g.spec.G) (you : Option Nat) (id : Nat) (L : Law) : Json × Bool :=
  let now := Preview.lawPreview s id L you g.nameOf
  let stale := match g.opened.find? (·.1 == id) with
    | some (_, at0) => (Preview.lawPreview at0 id L you g.nameOf).compress != now.compress
    | none => false
  (now, stale)

def proposalJson (g : Game) (s : State g.spec.G) (book : Describe.Book) (you : Option Nat) (p : OpenProposal) : Json :=
  let (kind, title, text, words, signers) := match p.body with
    | .law L => ("law", L.title, Rules.printProposal (.law L), ("description", Describe.json book L), ([] : List Nat))
    | .deal d => ("deal", d.title, Rules.printProposal (.deal d), ("english", Json.str (Text.dealText g.nameOf d)), d.signers)
  let can (e : Nat → Event) : Bool := match you with
    | some y => accepted s (e y)
    | none => false
  let seats := s.turnOrder.length
  let yes := p.yesCount
  let need := seats / 2 + 1
  let left := seats - p.votes.length
  let more := need - min need yes
  let (preview, stale) := match p.body with
    | .law L => previewFor g s you p.id L
    | .deal _ => (Json.null, false)
  Json.mkObj
    [ ("id", toJson p.id), ("by", toJson p.by_), ("kind", kind), ("title", title), ("text", text)
    , words
    , ("votes", Json.arr (p.votes.map fun v => Json.mkObj [("seat", toJson v.1), ("yes", toJson v.2)]).toArray)
    , ("signed", toJson p.signed), ("signers", toJson signers)
    , ("yesNeeded", toJson more), ("canPass", toJson (decide (more ≤ left)))
    , ("preview", preview), ("stale", toJson stale)
    , ("canVote", toJson (kind == "law" && can fun y => .vote y p.id false))
    , ("canSign", toJson (kind == "deal" && can fun y => .sign y p.id)) ]

def dealJson (g : Game) (s : State g.spec.G) (you : Option Nat) (d : ActiveDeal) : Json :=
  Json.mkObj
    [ ("id", toJson d.id), ("title", d.deal.title), ("english", Text.dealText g.nameOf d.deal)
    , ("lastRound", toJson d.lastRound), ("signers", toJson d.deal.signers)
    , ("text", Rules.printProposal (.deal d.deal))
    , ("canExit", toJson (match you with
        | some y => accepted s (.exit y d.id)
        | none => false)) ]

def offerJson (s : State G) (you : Option Nat) (o : Offer) : Json :=
  Json.mkObj
    [ ("id", toJson o.id), ("from", toJson o.src), ("to", toJson o.to)
    , ("give", bundleJson o.give), ("get", bundleJson o.get)
    , ("canAccept", toJson (match you with
        | some y => accepted s (.move y (.accept o.id))
        | none => false))
    , ("canCancel", toJson (match you with
        | some y => accepted s (.move y (.cancel o.id))
        | none => false)) ]

/-- The sample laws are written for the Island's pieces and resources. A game with those can use them. -/
def samplesJson (g : Game) : Json :=
  if !g.spec.samples then Json.arr #[] else
  -- A game with a founding law on the roll does not need a sample law about the roll.
  let rollRule (L : Law) : Bool := L.clauses.any fun | .onRoll _ => true | _ => false
  let hasRollRule := g.spec.G.foundingLaws.any rollRule
  Json.arr (Rules.sampleLaws.filterMap fun (id, text) =>
    match g.parse text with
    | .ok (.law L) =>
      if hasRollRule && rollRule L then none
      else some (Json.mkObj [("id", id), ("title", L.title), ("text", text)])
    | _ => none).toArray

def lineJson (l : Line) : Json :=
  Json.mkObj [("event", toJson l.event), ("actor", toJson l.actor), ("text", l.text),
    ("round", toJson l.round), ("kind", l.kind), ("major", toJson l.major)]

def decisionJson (book : Describe.Book) (d : Decision) : Json :=
  Json.mkObj
    [ ("id", toJson d.id), ("by", toJson d.by_), ("title", d.law.title), ("description", Describe.json book d.law)
    , ("text", Rules.printProposal (.law d.law))
    , ("votes", Json.arr (d.votes.map fun v => Json.mkObj [("seat", toJson v.1), ("yes", toJson v.2)]).toArray)
    , ("outcome", d.outcome), ("round", toJson d.round), ("event", toJson d.event)
    , ("pick", toJson (Scene.lawPick d.id).toNat) ]

def lawJson (g : Game) (book : Describe.Book) (x : Nat × Law) : Json :=
  let d := g.decisions.toList.find? (·.id == x.1)
  Json.mkObj
    [ ("id", toJson x.1), ("title", x.2.title), ("description", Describe.json book x.2)
    , ("text", Rules.printProposal (.law x.2))
    , ("by", toJson (d.map (·.by_))), ("round", toJson (d.map (·.round)))
    , ("votes", match d with
        | some v => Json.arr (v.votes.map fun w => Json.mkObj [("seat", toJson w.1), ("yes", toJson w.2)]).toArray
        | none => Json.arr #[])
    , ("pick", toJson (Scene.lawPick x.1).toNat) ]

def colorHex (c : UInt32) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  let n := c.toNat
  String.ofList ('#' :: ((List.range 6).reverse.map fun i => digit ((n >>> (4 * i)) % 16)))

/-- Everything one seat sees. A game's own seed stays hidden until the game ends. -/
def view (g : Game) (code : String) (you : Option Nat) (drafting : List Nat) (book : Describe.Book) : Json :=
  let G := g.spec.G
  let showPersona := you.isNone && g.openToSpectators
  let common : List (String × Json) :=
    [ ("code", code), ("version", toJson g.events), ("you", toJson you)
    , ("game", Json.mkObj [("id", g.spec.id), ("name", g.spec.name), ("blurb", g.spec.blurb), ("word", g.spec.layout.word)])
    , ("started", toJson g.room.started), ("maxSeats", toJson g.room.maxSeats)
    , ("minSeats", toJson g.room.minSeats), ("filled", toJson g.room.filled)
    , ("board", boardJson g.spec)
    , ("resources", toJson (goodsOf G))
    , ("seatColors", toJson (Scene.seatColors.map colorHex))
    , ("drafting", toJson drafting)
    , ("described", toJson (Describe.finished book))
    , ("fingerprint", commitmentOf g.serverSeed)
    , ("chronicle", Json.arr (g.chronicle.map lineJson)) ]
  match g.state with
  | none =>
    Json.mkObj (common ++
      [ ("phase", toJson "lobby"), ("seats", Json.arr ((List.range g.room.filled).map (seatJson g none showPersona)).toArray) ])
  | some s =>
    let isCounterTrade : Move → Bool
      | .bankTrade a b => markRes G a || markRes G b
      | _ => false
    let legal := match you with
      | some y => (Engine.legalMoves G s y).filter (!isCounterTrade ·)
      | none => []
    Json.mkObj (common ++
      [ ("phase", toJson (phaseText s.phase)), ("round", toJson s.round), ("rounds", toJson G.rounds)
      , ("turn", toJson s.currentSeat), ("lastRoll", toJson s.lastRoll)
      , ("rollsMade", toJson s.rollsMade)
      , ("target", toJson G.targetPoints), ("bankRate", toJson s.rules.bankRate)
      , ("fee", feeJson s you)
      , ("prompt", promptOf g s you legal)
      , ("seats", Json.arr (s.turnOrder.map (seatJson g (some s) showPersona)).toArray)
      , ("pieces", Json.arr (s.pieces.map pieceJson).toArray)
      , ("pieceDefs", Json.arr (s.rules.pieces.map (pieceDefJson s you legal)).toArray)
      , ("treasury", handJson s .treasury), ("bank", handJson s .bank)
      , ("legalMoves", Json.arr (legal.map (moveEntry g.spec.layout s)).toArray)
      , ("proposals", Json.arr (s.openProposals.map (proposalJson g s book you)).toArray)
      , ("laws", Json.arr (s.laws.map (lawJson g book)).toArray)
      , ("decisions", Json.arr (g.decisions.toList.map (decisionJson book)).toArray)
      , ("deals", Json.arr (s.deals.map (dealJson g s you)).toArray)
      , ("offers", Json.arr (s.offers.map (offerJson s you)).toArray)
      , ("samples", samplesJson g)
      , ("winner", toJson s.winner)
      , ("actionsLeft", toJson (match you with
          | some y => maxActionsPerTurn - s.actionsThisTurn y
          | none => 0))
      , ("serverSeed", if s.phase == .ended then toJson g.serverSeed.toNat else Json.null)
      , ("nonces", if s.phase == .ended then toJson (g.nonces.map (·.toNat)) else Json.null) ])

/-- Add a field to a view. -/
def withField (j : Json) (k : String) (v : Json) : Json :=
  match j with
  | .obj kvs => .obj (kvs.insert k v)
  | other => other

/-- A view with how many lines of talk the table has, so a page knows when to fetch them. -/
def withTalkCount (j : Json) (n : Nat) : Json := withField j "talkCount" (toJson n)

/-- A view as a step of a replay: which log entry this is, of how many. -/
def withReplay (j : Json) (at_ total : Nat) : Json :=
  withField j "replay" (Json.mkObj [("at", toJson at_), ("total", toJson total)])

/-- What the proposer judges: Claude's description, any stated difference, the consequences at this
table, and the rule source. The same description, consequences and source go to the table when the rule
is proposed. The difference is the clerk's note on how the rule differs from the player's request. It
says nothing about the description. A deal has a statement from Lean in place of a description. -/
def reviewJson (g : Game) (book : Describe.Book) (you : Nat) (formal : String) (difference : Option String) : Json :=
  match g.parse formal, g.state with
  | .ok p, some s =>
    let (kind, title, words, preview) := match p with
      | .law L => ("law", L.title, ("description", Describe.json book L), Preview.draftPreview s s.nextProposalId L you g.nameOf)
      | .deal d => ("deal", d.title, ("statement", Json.str (Text.dealText g.nameOf d)), Json.null)
    Json.mkObj
      [ ("kind", kind), ("title", title), words, ("difference", toJson difference)
      , ("preview", preview), ("text", Rules.printProposal p)
      , ("fee", if kind == "law" then feeJson s (some you) else Json.null)
      , ("canPropose", toJson (s.phase == .actions)) ]
  | _, _ => Json.null

/-- A draft as the screen reads it. It says only what has really happened. -/
def draftJson (g : Game) (book : Describe.Book) (you : Nat) (job : Formalize.Job) (st : Formalize.JobState) (now : Nat) : Json :=
  let base : List (String × Json) :=
    [ ("id", toJson job.id), ("words", st.suggestedWords.getD job.words)
    , ("mode", if job.suggest then "suggest" else "draft"), ("why", toJson st.why)
    , ("whyStale", toJson (job.suggest && st.why.isSome && st.atEvent != g.events))
    , ("stage", st.stage), ("attempt", toJson st.attempt)
    , ("retryReason", toJson st.retryReason), ("elapsedMs", toJson (now - job.startedMs))
    , ("quietMs", toJson (now - st.lastEventMs))
    , ("thinking", toJson ((String.ofList (st.thinking.toList.reverse.take 240).reverse)))
    , ("text", st.text)
    , ("usage", Json.mkObj
        [ ("input", toJson st.inputTokens), ("cacheRead", toJson st.cacheReadTokens)
        , ("cacheWrite", toJson st.cacheWriteTokens), ("output", toJson st.outputTokens) ]) ]
  let final : List (String × Json) := match st.final with
    | none => [("outcome", Json.null)]
    | some (.ready formal diff viaClaude) =>
      [("outcome", "ready"), ("viaClaude", toJson viaClaude), ("review", reviewJson g book you formal diff)]
    | some (.refused why) => [("outcome", "refused"), ("reason", why)]
    | some (.failed msg) => [("outcome", "failed"), ("reason", msg)]
    | some .cancelled => [("outcome", "cancelled")]
  Json.mkObj (base ++ final)

/-! ## Why something was refused -/

def shortText (b : Bundle) : String := Text.bundleText b

/-- Say a rejected event in plain language: what happened, and why. -/
def explain (g : Game) (ev : Json) (raw : String) : String :=
  let seat := jNat ev "seat"
  let t := (jStr ev "t").getD ""
  let moveT := (jField ev "move").bind (jStr · "t")
  match g.state, seat with
  | some s, some y =>
    if raw == "an entry cannot be posted in full" then
      if t == "propose" then
        s!"You cannot pay the fee of {shortText g.spec.G.lawFee}. You need {shortText (shortOf s y g.spec.G.lawFee)} more."
      else if moveT == some "place" then
        let k := ((jField ev "move").bind (jStr · "kind")).getD "piece"
        s!"You cannot pay for {Text.article k}. You need {shortText (shortOf s y (s.costOf k))} more."
      else if moveT == some "bankTrade" then
        s!"You need {s.rules.bankRate} {((jField ev "move").bind (jStr · "give")).getD "of that resource"} to trade with the bank."
      else if moveT == some "accept" then
        "One side no longer has what the offer needs."
      else if t == "sign" then
        "A signer cannot pay their deposit, so the deal cannot start yet."
      else "A payment could not be made in full, so nothing happened."
    else if raw == "this law cannot pass" then
      match (jStr ev "text").map g.parse with
      | some (.ok (.law L)) => s!"The constitution refuses this law. {Formalize.problemsText (lawProblems g.spec.G s L)}"
      | _ => "The constitution refuses this law."
    else if raw == "this deal cannot run" then
      match (jStr ev "text").map g.parse with
      | some (.ok (.deal d)) => s!"This deal cannot run. {Formalize.problemsText (dealProblems s d)}"
      | _ => "This deal cannot run."
    else if raw == "this seat cannot act now" then
      if s.turnOrder.contains y then "You have used all your actions this turn." else "You do not have a seat in this game."
    else if raw == "this seat has too many open proposals" then
      s!"You already have {maxOpenPerSeat} proposals before the table. Wait for one to finish."
    else if raw == "only a signer can propose a deal" then "You can only propose a deal you sign."
    else if raw == "only the current seat can end its turn" then "It is not your turn."
    else if raw == "a vote is final" then "You have already voted. A vote is final."
    else if raw == "this piece cannot be placed there now" then "You cannot build that there now."
    else if raw == "this setup piece cannot be placed there now" then "You cannot place that there."
    else Formalize.sentence raw
  | _, _ => Formalize.sentence raw

/-- The summary on the table list. -/
def summary (g : Game) (code : String) : Json :=
  let phase := match g.state with
    | some s => phaseText s.phase
    | none => "lobby"
  Json.mkObj [("code", code), ("events", toJson g.events), ("game", g.spec.id), ("filled", toJson g.room.filled),
    ("seats", toJson g.room.maxSeats), ("started", toJson g.room.started), ("phase", phase)]

/-- What a player's text means, and whether it can pass now. -/
def checkText (g : Game) (text : String) : Json :=
  match g.parse text with
  | .error e => Json.mkObj [("ok", toJson false), ("error", e)]
  | .ok p =>
    let english : List (String × Json) := match p with
      | .law _ => []
      | .deal d => [("english", Json.str (Text.dealText g.nameOf d))]
    let problems := match g.state, p with
      | some s, .law L => lawProblems g.spec.G s L
      | some s, .deal d => dealProblems s d
      | none, _ => ["the game has not started"]
    Json.mkObj ([("ok", toJson true), ("problems", toJson problems),
      ("text", Rules.printProposal p)] ++ english)

end CharterServer.View
