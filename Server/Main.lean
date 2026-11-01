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
import Server.Mirror
import Server.Spend

/-!
`charter-server`: the HTTP front end.

The routes. Tables and their logs are in `Server/Table.lean`, and the seats the server plays are in
`Server/Driver.lean`. Clients poll `/view`. Adapted from the older game's `Server/Main.lean`.

A game code is what lets a person reach a table, so no public route lists the codes. `GET /api/games`
answers only with `CHARTER_LIST_GAMES` set or in a spectate run, and the tests use that.
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

def clientKey (req : Req) : IO UInt64 :=
  Spend.keyOf (headerOf req "x-charter-client-ip")

def handleCreate (ctx : Ctx) (req : Req) (body : Json) : ContextAsync Resp := do
  let ip ← clientKey req
  if let some why ← Spend.admitGame ip then return ← respondErr why .tooManyRequests
  let seats := (jNat body "seats").getD 4
  let code ← randomCode
  let game := (jStr body "game").getD islandSpec.id
  let ev := Json.mkObj [("t", "create"), ("code", code), ("seats", toJson seats), ("game", game),
    ("_serverSeed", toJson (← randomNat64))]
  match ← addGame ctx ev with
  | .error err => respondJson (errJson err)
  | .ok e =>
    Spend.setPayer code ip
    respondJson (okJson [("code", code), ("fingerprint", commitmentOf e.game.serverSeed)])

def handleJoin (ctx : Ctx) (req : Req) (code : String) (body : Json) : ContextAsync Resp := do
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
    markPresent ctx code e'.game (clientKey req)
    startIfFull ctx code
    respondJson (okJson [("seat", toJson (seatOf e' (some token))), ("token", token)])

/-- A Claude seat joins with a persona the table does not have yet. The seed is in the join event. -/
def handleClaude (ctx : Ctx) (req : Req) (code : String) (body : Json) : ContextAsync Resp := do
  Spend.setPayer code (← clientKey req)
  if let some why ← Spend.resting? code then return ← respondErr why .tooManyRequests
  let token ← randomToken
  let nonce ← randomNat64
  let seed ← randomNat64
  let only := match jStr body "style" with
    | some st => [st]
    | none => []
  let mk : Entry → Except String Json := fun e =>
    let used := e.game.room.occupants.map (·.name)
    let usedStyles := e.game.personas.toList.filterMap (·.map (·.style))
    let choices := Persona.pick (UInt64.ofNat seed) 10 only e.game.spec.id
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
def seatEvent (ctx : Ctx) (req : Req) (code : String) (body : Json) (mk : Entry → Nat → Except String Json) :
    ContextAsync Resp := do
  let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
  let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
  markPresent ctx code e.game (clientKey req)
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
  return View.draftJson e.game (← bookOf ctx e.code) seat job st (← IO.monoMsNow)

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

/-- A scene stream, or nothing if the client says it has these bytes already. Most of what changes a
table changes no picture, and a late scene is the largest thing a table sends. -/
def respondScene (req : Req) (bytes : ByteArray) : Async Resp := do
  let tag := hexOf (hash bytes)
  if req.line.uri.query.get "have" == some tag then
    respond .noContent sceneType .empty
  else
    respond .ok sceneType bytes [("X-Scene-Tag", tag)]

/-- How many real tokens this table's Claude seats spent, from its seat log. Only for a finished table
with Claude seats: anything else has no such line. It is a record of what happened, and no rule reads it. -/
def realTokens (ctx : Ctx) (code : String) (g : Game) : IO Json := do
  let ended := match g.state with
    | some s => s.phase == .ended
    | none => false
  if !ended || !(List.range g.kinds.size).any g.isClaude then return Json.null
  let records ← seatRecords ctx code
  let spent := records.toList.filter fun r => jStr r "k" == some "call" || jStr r "k" == some "draft"
  let sum (k : String) : Nat := (spent.map fun r => (jNat r k).getD 0).sum
  return toJson (sum "input" + sum "cacheRead" + sum "cacheWrite" + sum "output")

def route (ctx : Ctx) (req : Req) : ContextAsync Resp := do
  let segs := req.line.uri.path.toDecodedSegments.toList.filter (· != "")
  let q := req.line.uri.query
  let isPost := req.line.method == .post
  -- The page sends the seat token in a header, so it stays out of URLs and anything that logs them.
  let token := (headerOf req "x-charter-token").orElse fun _ => q.get "token"
  match segs with
  | ["api", "games"] =>
    if isPost then handleCreate ctx req (← readBody req)
    else if ctx.noDrivers || (← IO.getEnv "CHARTER_LIST_GAMES").isSome then
      let all ← ctx.table.atomically do
        return (← get).toList.map fun (c, e) => View.summary e.game c
      respondJson (Json.arr all.toArray)
    else respondErr "unknown route" .notFound
  | ["api", "games", code] =>
    let code := code.toUpper
    let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
    respondJson (View.summary e.game code)
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
          respondJson (View.withField (View.withReplay (View.view g code none [] (← bookOf ctx code)) at_ e.events.size) "realTokens" (← realTokens ctx code g))
      | none =>
        -- This is how the server knows who is here. A table with no people, held since a restart,
        -- waits only for someone to watch it.
        if (seatOf e token).any e.game.isHuman then
          markPresent ctx code e.game (clientKey req)
        else if e.game.humanSeats.isEmpty && (← ctx.stopped.get).contains code then
          markPresent ctx code e.game (clientKey req)
        let since := (q.get "since").bind String.toNat?
        let left ← turnLeftMs ctx e.game code
        let resting := (← Spend.resting? code).map (Json.str ·) |>.getD Json.null
        let paused := toJson (← isPaused ctx code e.game)
        let book ← bookOf ctx code
        -- A description that has just finished changes the view with no new game event.
        let seenDescriptions := match (q.get "described").bind String.toNat? with
          | some n => n == Describe.finished book
          | none => true
        if since == some e.game.events && seenDescriptions then
          respondJson (Json.mkObj [("unchanged", toJson true), ("version", toJson e.game.events),
            ("talkCount", toJson e.talk.size), ("turnLeftMs", toJson left), ("drafting", toJson (← draftingSeats ctx code)),
            ("resting", resting), ("paused", paused)])
        else
          let v := View.withTalkCount (View.view e.game code (seatOf e token) (← draftingSeats ctx code) book) e.talk.size
          respondJson (View.withField (View.withField (View.withField (View.withField v "turnLeftMs" (toJson left)) "resting" resting) "paused" paused) "realTokens" (← realTokens ctx code e.game))
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
          respondScene req (Scene.sceneBytes g.spec.layout s none .none)
      | none =>
        let s := e.game.state.getD (emptyBoard e.game.spec)
        respondScene req (Scene.sceneBytes e.game.spec.layout s (seatOf e token) show_)
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
      Spend.setPayer code (← clientKey req)
      discard <| startDraft ctx code seat words
      respondJson (← draftView ctx e seat)
    | "suggest", true =>
      let body ← readBody req
      let some e ← findEntry ctx code | respondErr s!"no game {code}" .notFound
      let some seat := seatOf e (jStr body "token") | respondErr "bad or missing token" .unauthorized
      match e.game.state with
      | some s =>
        if s.phase != .actions then
          return ← respondErr "The clerk can suggest a rule only while the game is being played."
      | none => return ← respondErr "The game has not started."
      Spend.setPayer code (← clientKey req)
      discard <| startSuggest ctx code seat
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
    | "join", true => handleJoin ctx req code (← readBody req)
    | "bot", true => handleBot ctx code
    | "claude", true => handleClaude ctx req code (← readBody req)
    | "start", true =>
      let body ← readBody req
      seatEvent ctx req code body fun _ _ => .ok (Json.mkObj [("t", "start")])
    | "move", true =>
      let body ← readBody req
      seatEvent ctx req code body fun _ seat => do
        let some m := jField body "move" | throw "missing move"
        return Json.mkObj [("t", "move"), ("seat", toJson seat), ("move", m)]
    | "propose", true =>
      let body ← readBody req
      seatEvent ctx req code body fun _ seat => do
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
      seatEvent ctx req code body fun _ seat => do
        let some id := jNat body "id" | throw "missing id"
        return Json.mkObj [("t", "vote"), ("seat", toJson seat), ("id", toJson id),
          ("yes", toJson ((jBool body "yes").getD false))]
    | "sign", true =>
      let body ← readBody req
      seatEvent ctx req code body fun _ seat => do
        let some id := jNat body "id" | throw "missing id"
        return Json.mkObj [("t", "sign"), ("seat", toJson seat), ("id", toJson id)]
    | "exit", true =>
      let body ← readBody req
      seatEvent ctx req code body fun _ seat => do
        let some id := jNat body "dealId" | throw "missing dealId"
        return Json.mkObj [("t", "exit"), ("seat", toJson seat), ("dealId", toJson id)]
    | _, _ => respondErr "unknown route" .notFound
  | ["api", "island"] =>
    respond .ok sceneType (Scene.sceneBytes islandSpec.layout (emptyBoard islandSpec) none .none)
  | ["api", "defs"] =>
    respondJson (Json.arr (gameSpecs.map fun d =>
      Json.mkObj [("id", d.id), ("name", d.name), ("blurb", d.blurb), ("minSeats", toJson d.minSeats),
        ("maxSeats", toJson d.maxSeats), ("look", View.lookJson d.layout.theme)]).toArray)
  | ["api", "defs", id, "scene"] =>
    match specOf? (some id) with
    | some d => respond .ok sceneType (Scene.sceneBytes d.layout (emptyBoard d) none .none)
    | none => respondErr "unknown game" .notFound
  | "api" :: _ => respondErr "unknown route" .notFound
  | ["assets", name] => serveMeshFile (ctx.webRoot.parent.getD ".") name meshFolderOf
  | "v" :: build :: rest => serveBuild ctx.webRoot build rest
  | rest => serveStatic req ctx.webRoot rest

def handler (ctx : Ctx) (req : Req) : ContextAsync Resp := do
  try
    route ctx req
  catch err =>
    IO.eprintln s!"error: {err}"
    respondErr (toString err) .internalServerError

/-- Files the server reads while it runs, under its root. Some are read only when a Claude seat or the
clerk first needs them, and a missing one would then look like an empty prompt. So check them at start. -/
def requiredFiles : List String :=
  ["Server/formalizer.md", "Server/describer.md", "Server/player_rules.md", "web/index.html", "web/app.js", "web/app.css",
   "web/board2d.js", "web/icons.js", "web/look.js", "web/vendor/player.js", "web/vendor/meshfile.js"]

/-- Stop now, and say why. -/
def die {α : Type} (msg : String) : IO α := do
  IO.eprintln s!"charter-server: {msg}"
  (← IO.getStderr).flush
  IO.Process.exit 1

def checkRequiredFiles (root : System.FilePath) : IO Unit := do
  let mut missing : List String := []
  for f in requiredFiles do
    let path := root / f
    let good ← if !(← path.pathExists) then pure false
      else pure !(← IO.FS.readFile path).trimAscii.isEmpty
    if !good then missing := missing ++ [f]
  for f in meshFiles do
    if !(← (root / f).pathExists) then missing := missing ++ [f]
  if !missing.isEmpty then
    die s!"these files are missing or empty under {root}: {", ".intercalate missing}. Set CHARTER_ROOT to the folder that holds them."

/-- The address to listen on. Only this machine by default. -/
def bindAddress : IO Std.Net.IPv4Addr := do
  let text := (← IO.getEnv "CHARTER_BIND").getD "127.0.0.1"
  match (text.splitOn ".").mapM String.toNat? with
  | some [a, b, c, d] =>
    if a < 256 && b < 256 && c < 256 && d < 256 then
      return .ofParts a.toUInt8 b.toUInt8 c.toUInt8 d.toUInt8
    else die s!"CHARTER_BIND must be an IPv4 address, and it is {text}"
  | _ => die s!"CHARTER_BIND must be an IPv4 address, and it is {text}"

/-- Fill the data folder from storage, before anything reads it. A short failure is worth waiting out.
After that the server stops: it must not run with games missing. -/
def restoreOrDie (url : String) (dataDir : System.FilePath) : IO Mirror.Mirror := do
  let mut lastError := ""
  for attempt in [0:6] do
    if attempt > 0 then IO.sleep 5000
    try
      let start ← IO.monoMsNow
      let (m, objects) ← Mirror.restore url dataDir
      IO.println s!"charter-server: restored {objects} objects from storage in {(← IO.monoMsNow) - start} ms"
      (← IO.getStdout).flush
      return m
    catch err =>
      lastError := toString err
      IO.eprintln s!"charter-server: restore failed, attempt {attempt + 1}: {err}"
  die s!"could not restore the games from storage, so the server will not start. {lastError}"

/-- On SIGTERM, which is how the platform stops a container: copy everything to storage, and exit. The
locks are held to the end, so no move can be accepted after the last copy. -/
def exitOnSigterm (ctx : Ctx) (mirror : Option Mirror.Mirror) : IO Unit := do
  let signal ← Std.Async.Signal.Waiter.mk .sigterm false
  let task ← signal.wait
  discard <| IO.mapTask (β := Unit) (prio := .dedicated) (t := task) fun _ => do
    IO.println "charter-server: stopping"
    (← IO.getStdout).flush
    ctx.table.atomically do
      ctx.seatLogs.atomically do
        ctx.clerkLogs.atomically do
          if let some m := mirror then
            try
              Mirror.flush m (all := true)
              IO.println "charter-server: everything is in storage"
            catch err =>
              IO.eprintln s!"charter-server: the last copy failed: {err}"
          (← IO.getStdout).flush
          (IO.Process.exit 0 : IO Unit)

end CharterServer

open CharterServer in
def main (_args : List String) : IO Unit := do
  let port := ((← IO.getEnv "PORT").bind String.toNat?).getD 8787
  let bind ← bindAddress
  let root : System.FilePath := (← IO.getEnv "CHARTER_ROOT").getD "."
  let dataDir : System.FilePath := (← IO.getEnv "CHARTER_DATA").getD (root / "data" / "games").toString
  let mirrorUrl := (← IO.getEnv "CHARTER_MIRROR_URL").filter (!·.isEmpty)
  checkRequiredFiles root
  if mirrorUrl.isSome || (← Formalize.settings root).key.isSome then
    let works ← try
        pure ((← IO.Process.output { cmd := "curl", args := #["--version"] }).exitCode == 0)
      catch _ => pure false
    if !works then die "curl is needed to reach Claude and storage, and it cannot be run."
  IO.FS.createDirAll dataDir
  let mirror ← mirrorUrl.mapM (restoreOrDie · dataDir)
  let showOnly := (← IO.getEnv "CHARTER_SHOW_ONLY").isSome
  if !showOnly then Spend.configure dataDir
  let tbl ← loadAll dataDir
  let delay := ((← IO.getEnv "CHARTER_BOT_DELAY_MS").bind String.toNat?).getD 600
  let hold := ((← IO.getEnv "CHARTER_VOTE_HOLD_MS").bind String.toNat?).getD 30000
  let ctx ← Ctx.new tbl root dataDir delay hold (← seatSettingsFromEnv) showOnly
  IO.println s!"charter-server: {tbl.size} games loaded; http://{bind}:{port}/"
  (← IO.getStdout).flush
  for (code, _) in tbl.toList do
    restoreDescriptions ctx code
    if !showOnly then
      Seat.restoreMinds ctx code
  if !showOnly then holdClaudeTables ctx
  for (code, _) in tbl.toList do
    kickBots ctx code
  startTurnTimer ctx
  if let some m := mirror then
    let every := ((← IO.getEnv "CHARTER_MIRROR_INTERVAL_MS").bind String.toNat?).getD 1000
    discard <| IO.asTask (prio := .dedicated) (Mirror.loop m every)
  exitOnSigterm ctx mirror
  Std.Async.Async.block do
    let addr : Std.Net.SocketAddress := .v4 ⟨bind, port.toUInt16⟩
    let server ← Std.Http.Server.serve addr (Std.Http.Server.Handler.ofFn (handler ctx))
    server.waitShutdown
