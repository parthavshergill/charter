import Std.Http
import Lean.Data.Json
import EventLog
import Server.Util
import Server.Http
import Server.Game
import Server.Bots
import Server.View
import Server.Table
import Server.Driver

/-!
`charter-server`: the HTTP front end.

The routes. Tables and their logs are in `Server/Table.lean`, and the seats the server plays are in
`Server/Driver.lean`. Clients poll `/view`. Adapted from the older game's `Server/Main.lean`.
-/

namespace CharterServer
open Std Async Std.Http Lean
open Charter CharterServer.Game

def readBody (req : Req) : ContextAsync Json := do
  let s : String ← req.body.readAll (maximumSize := some 1000000)
  if s.trimAscii.isEmpty then return Json.mkObj []
  match Json.parse s with
  | .ok j => return j
  | .error e => throw (IO.userError s!"bad JSON body: {e}")

def resultJson (r : Except String Entry) : Async Resp :=
  match r with
  | .ok e => respondJson (okJson [("version", toJson e.game.events)])
  | .error err => respondJson (errJson err)

def handleCreate (ctx : Ctx) (body : Json) : ContextAsync Resp := do
  let seats := (jNat body "seats").getD 4
  let code ← randomCode
  let game := (jStr body "game").getD islandSpec.id
  let ev := Json.mkObj [("t", "create"), ("code", code), ("seats", toJson seats), ("game", game),
    ("_serverSeed", toJson (← randomNat64))]
  match ← addGame ctx ev with
  | .error err => respondJson (errJson err)
  | .ok e => respondJson (okJson [("code", code), ("fingerprint", commitmentOf e.game.serverSeed)])

def handleJoin (ctx : Ctx) (code : String) (body : Json) : ContextAsync Resp := do
  let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
  if let some seat := seatOf e (jStr body "token") then
    return ← respondJson (okJson [("seat", toJson seat), ("token", (jStr body "token").getD "")])
  let name := ((jStr body "name").getD "").trimAscii.toString
  if name.isEmpty then return ← respondErr "a player needs a name"
  -- A person's own nonce is what stops the server from choosing the dice alone, so it must come from
  -- the client. The server makes nonces only for the seats it plays.
  let some nonce := jNat body "nonce" | respondErr "A player must send a nonce of their own."
  let token ← randomToken
  let ev := Json.mkObj [("t", "join"), ("name", name), ("kind", "human"),
    ("_token", token), ("nonce", toJson nonce)]
  match ← commit ctx code ev with
  | .error err => respondJson (errJson err)
  | .ok e' =>
    startIfFull ctx code
    respondJson (okJson [("seat", toJson (seatOf e' (some token))), ("token", token)])

/-- A Claude seat joins with a persona the table does not have yet. The seed is in the join event. -/
def handleClaude (ctx : Ctx) (code : String) (body : Json) : ContextAsync Resp := do
  let token ← randomToken
  let nonce ← randomNat64
  let seed ← randomNat64
  let only := match jStr body "style" with
    | some st => [st]
    | none => []
  let mk : Entry → Except String Json := fun e =>
    let used := e.game.room.occupants.map (·.name)
    let usedStyles := e.game.personas.toList.filterMap (·.map (·.style))
    let choices := Persona.pick (UInt64.ofNat seed) 10 only
    let unused := choices.filter fun p => !used.contains p.name
    let fresh := unused.filter fun p => !usedStyles.contains p.style
    match (fresh ++ unused).head? with
    | none => .error "no free persona"
    | some p =>
      .ok (Json.mkObj [("t", "join"), ("name", p.name), ("kind", "claude"), ("_token", token),
        ("nonce", toJson nonce), ("_persona", Persona.toJson' p), ("_personaSeed", toJson seed)])
  match ← commitRaw ctx code mk with
  | .error err => respondJson (errJson err)
  | .ok e' =>
    startIfFull ctx code
    kickBots ctx code
    respondJson (okJson [("seat", toJson (seatOf e' (some token)))])

def handleBot (ctx : Ctx) (code : String) : ContextAsync Resp := do
  let token ← randomToken
  let nonce ← randomNat64
  let mk : Entry → Except String Json := fun e =>
    .ok (Json.mkObj [("t", "join"), ("name", Bots.freshName e.game), ("kind", "bot"),
      ("_token", token), ("nonce", toJson nonce)])
  match ← commitRaw ctx code mk with
  | .error err => respondJson (errJson err)
  | .ok e' =>
    startIfFull ctx code
    kickBots ctx code
    respondJson (okJson [("seat", toJson (seatOf e' (some token)))])

/-- A seat-bound event: resolve the token, attach the seat, commit. -/
def seatEvent (ctx : Ctx) (code : String) (body : Json) (mk : Entry → Nat → Except String Json) :
    ContextAsync Resp := do
  let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
  let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
  match mk e seat with
  | .error err => respondJson (errJson err)
  | .ok ev =>
    match ← commit ctx code ev with
    | .ok e' => respondJson (okJson [("version", toJson e'.game.events)])
    | .error err => respondJson (errJson (View.explain e.game ev err))

def draftView (ctx : Ctx) (e : Entry) (seat : Nat) : IO Json := do
  let some job := (← ctx.drafts.get).get? (e.code, seat)
    | return Json.mkObj [("id", Json.null)]
  let st ← job.state.get
  return View.draftJson e.game seat job st (← IO.monoMsNow)

/-- The formal text of a proposal: typed, a sample, or the simple deal form. -/
def proposalText (body : Json) (seat : Nat) : Except String String := do
  if let some id := jStr body "sample" then
    match Rules.sampleLaws.find? (·.1 == id) with
    | some (_, text) => return text
    | none => throw s!"no sample law {id}"
  if let some text := jStr body "text" then return text
  if let some f := jField body "dealForm" then
    let some other := jNat f "with" | throw "a deal needs another seat"
    let rounds := (jNat f "rounds").getD 1
    let notice := (jNat f "exitNotice").getD 0
    let give := (jStr f "give").getD ""
    let giveN := (jNat f "giveN").getD 0
    let get := match jStr f "get", jNat f "getN" with
      | some r, some n => if r.isEmpty then none else some (r, n)
      | _, _ => none
    return Rules.printProposal (.deal (Rules.formDeal seat other rounds notice give giveN get))
  throw "a proposal needs text, a sample or a deal form"

def route (ctx : Ctx) (req : Req) : ContextAsync Resp := do
  let segs := req.line.uri.path.toDecodedSegments.toList.filter (· != "")
  let q := req.line.uri.query
  let isPost := req.line.method == .post
  let token := q.get "token"
  match segs with
  | ["api", "games"] =>
    if isPost then handleCreate ctx (← readBody req)
    else
      let all ← ctx.table.atomically do
        return (← get).toList.map fun (c, e) => View.summary e.game c
      respondJson (Json.arr all.toArray)
  | ["api", "games", code, action] =>
    let code := code.toUpper
    match action, isPost with
    | "view", false =>
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      match (q.get "at").bind String.toNat? with
      | some at_ =>
        -- A replay: the game after this many log entries, as a spectator sees it.
        let at_ := min at_ e.events.size
        match gameAt e at_ with
        | .error err => respondErr err
        | .ok g =>
          respondJson (View.withReplay (View.view g code none []) at_ e.events.size)
      | none =>
        let since := (q.get "since").bind String.toNat?
        let left ← turnLeftMs ctx e.game code
        if since == some e.game.events then
          respondJson (Json.mkObj [("unchanged", toJson true), ("version", toJson e.game.events),
            ("talkCount", toJson e.talk.size), ("turnLeftMs", toJson left), ("drafting", toJson (← draftingSeats ctx code))])
        else
          let v := View.withTalkCount (View.view e.game code (seatOf e token) (← draftingSeats ctx code)) e.talk.size
          respondJson (View.withField v "turnLeftMs" (toJson left))
    | "talk", false =>
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let at_ := (q.get "at").bind String.toNat?
      let viewer := if at_.isSome then none else seatOf e token
      let upTo (l : Talk.Line) : Bool := match at_ with
        | some n => l.event ≤ n
        | none => true
      let seen := e.talk.toList.filter fun l =>
        upTo l && Talk.canSee e.game.openToSpectators viewer l
      respondJson (okJson [("lines", Json.arr (seen.map Talk.lineJson).toArray), ("count", toJson e.talk.size)])
    | "talk", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
      let text := Talk.clean ((jStr body "text").getD "")
      if text.isEmpty then return ← respondErr "Say something first."
      let to := jNat body "to"
      if let some t := to then
        if t == seat || t ≥ e.game.room.filled then return ← respondErr "There is nobody in that seat to tell."
      addTalk ctx code (if to.isSome then "private" else "public") seat to text
      respondJson (okJson [])
    | "scene", false =>
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let show_ : Scene.MarkerFilter := match q.get "markers" with
        | some "none" => .none
        | some "all" | none => .all
        | some k => .kind k
      match (q.get "at").bind String.toNat? with
      | some at_ =>
        match gameAt e at_ with
        | .error err => respondErr err
        | .ok g =>
          let s := g.state.getD (emptyBoard g.spec)
          respond .ok "application/octet-stream" (Scene.sceneBytes g.spec.layout s none .none)
      | none =>
        let s := e.game.state.getD (emptyBoard e.game.spec)
        respond .ok "application/octet-stream" (Scene.sceneBytes e.game.spec.layout s (seatOf e token) show_)
    | "draft", false =>
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e token | respondErr "bad or missing token" .unauthorized
      respondJson (← draftView ctx e seat)
    | "draft", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
      let words := match jStr body "sample" with
        | some id => ((Rules.sampleLaws.find? (·.1 == id)).map (·.2)).getD ""
        | none => (jStr body "words").getD ""
      if words.trimAscii.isEmpty then return ← respondErr "Write the rule you want first."
      if words.length > Clerk.maxRequestChars then
        return ← respondErr s!"That is too long for the clerk. Keep it under {Clerk.maxRequestChars} characters."
      if e.game.state.isNone then return ← respondErr "The game has not started."
      discard <| startDraft ctx code seat words
      respondJson (← draftView ctx e seat)
    | "draft-cancel", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
      if let some job := (← ctx.drafts.get).get? (code, seat) then
        if (← job.state.get).final.isNone then
          stopDraft job
          job.state.modify fun st => { st with stage := "done", final := some .cancelled }
      respondJson (okJson [])
    | "draft-clear", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
      if let some job := (← ctx.drafts.get).get? (code, seat) then stopDraft job
      ctx.drafts.modify (·.erase (code, seat))
      respondJson (okJson [])
    | "events", false =>
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let from_ := ((q.get "from").bind String.toNat?).getD 0
      respondJson (Json.arr ((e.events.extract from_ e.events.size).map stripPrivate))
    | "join", true => handleJoin ctx code (← readBody req)
    | "bot", true => handleBot ctx code
    | "claude", true => handleClaude ctx code (← readBody req)
    | "start", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ _ => .ok (Json.mkObj [("t", "start")])
    | "move", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ seat => do
        let some m := jField body "move" | throw "missing move"
        return Json.mkObj [("t", "move"), ("seat", toJson seat), ("move", m)]
    | "propose", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ seat => do
        let text ← proposalText body seat
        return Json.mkObj [("t", "propose"), ("seat", toJson seat), ("text", text)]
    | "check", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let seat := (seatOf e (jStr body "token")).getD 0
      match proposalText body seat with
      | .ok text => respondJson (View.checkText e.game text)
      | .error err => respondJson (errJson err)
    | "vote", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ seat => do
        let some id := jNat body "id" | throw "missing id"
        return Json.mkObj [("t", "vote"), ("seat", toJson seat), ("id", toJson id),
          ("yes", toJson ((jBool body "yes").getD false))]
    | "sign", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ seat => do
        let some id := jNat body "id" | throw "missing id"
        return Json.mkObj [("t", "sign"), ("seat", toJson seat), ("id", toJson id)]
    | "exit", true =>
      let body ← readBody req
      seatEvent ctx code body fun _ seat => do
        let some id := jNat body "dealId" | throw "missing dealId"
        return Json.mkObj [("t", "exit"), ("seat", toJson seat), ("dealId", toJson id)]
    | _, _ => respondErr "unknown route" .notFound
  | ["api", "island"] =>
    respond .ok "application/octet-stream" (Scene.sceneBytes islandSpec.layout (emptyBoard islandSpec) none .none)
  | ["api", "defs"] =>
    respondJson (Json.arr (gameSpecs.map fun d => Json.mkObj [("id", d.id), ("name", d.G.name)]).toArray)
  | "api" :: _ => respondErr "unknown route" .notFound
  | rest => serveStatic ctx.webRoot rest

def handler (ctx : Ctx) (req : Req) : ContextAsync Resp := do
  try
    route ctx req
  catch err =>
    IO.eprintln s!"error: {err}"
    respondErr (toString err) .internalServerError

end CharterServer

open CharterServer in
def main (_args : List String) : IO Unit := do
  let port := ((← IO.getEnv "PORT").bind String.toNat?).getD 8787
  let root : System.FilePath := (← IO.getEnv "CHARTER_ROOT").getD "."
  let dataDir : System.FilePath := (← IO.getEnv "CHARTER_DATA").getD (root / "data" / "games").toString
  IO.FS.createDirAll dataDir
  let tbl ← loadAll dataDir
  let delay := ((← IO.getEnv "CHARTER_BOT_DELAY_MS").bind String.toNat?).getD 600
  let hold := ((← IO.getEnv "CHARTER_VOTE_HOLD_MS").bind String.toNat?).getD 30000
  let showOnly := (← IO.getEnv "CHARTER_SHOW_ONLY").isSome
  let ctx ← Ctx.new tbl root dataDir delay hold (← seatSettingsFromEnv) showOnly
  IO.println s!"charter-server: {tbl.size} games loaded; http://127.0.0.1:{port}/"
  (← IO.getStdout).flush
  for (code, _) in tbl.toList do
    if !showOnly then
      Seat.restoreMinds ctx code
    kickBots ctx code
  startTurnTimer ctx
  Std.Async.Async.block do
    let addr : Std.Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩
    let server ← Std.Http.Server.serve addr (Std.Http.Server.Handler.ofFn (handler ctx))
    server.waitShutdown
