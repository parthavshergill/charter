import Lean.Data.Json
import EventLog
import Server.Util

/-!
# The mirror: every log, copied to object storage

A container's disk is lost when it sleeps. So this thread copies each log's new rows to R2, and a new
container reads them back before it serves anyone. Logs only ever grow, and a row never changes, so a
copy is just "the rows after the last one copied".

**It never blocks a move.** `commitRaw` writes to local SQLite as before and returns. This thread reads
through its own SQLite connection, which WAL mode lets it do while a writer is busy. It reads rows
through SQLite, never the `.db` file, because recent rows sit in the WAL.

**It finds logs by looking at the data folder**, so a new kind of log needs only a new entry in
`logExtensions`. A log with no change since the last look costs a few file checks.

**Objects.** `v1/<file>/<first>-<count>.jsonl` holds `count` rows from row `first`, one JSON string per
line. New rows make a new object. A log with many objects, or a log gone quiet with more than one, is
written again as a single object and its old objects are deleted. A crash between those two steps
leaves objects that overlap, and restoring allows for that.

**The storage end.** There is no key for R2 in the container. Requests go to `CHARTER_MIRROR_URL`, and
the Worker answers them with its R2 binding (`cloudflare/src/index.ts`): `PUT`, `GET` and `DELETE` on
`/o/<key>`, and `GET /list`, which answers `{"keys": [...], "cursor": ...}`.

**What a hard kill can lose:** rows accepted since the last copy, which is about one interval plus one
upload. On SIGTERM the server copies everything and then exits, so a sleep or a rollout loses nothing.
What survives is always a prefix of each log, so a game replays to a real earlier position.
-/

namespace CharterServer.Mirror
open Lean

/-- The files that are logs. `-wal` and `-shm` files are not on this list. -/
def logExtensions : List String := ["db", "talk", "clerk", "seats", "ledger"]

def isLog (fileName : String) : Bool :=
  !fileName.startsWith "." && logExtensions.any fun x => fileName.endsWith s!".{x}"

/-- One stored object. -/
structure Obj where
  first : Nat
  count : Nat
  deriving Inhabited, BEq

/-- What changes on disk when a row is written. -/
structure Sig where
  size : UInt64 := 0
  walSize : UInt64 := 0
  walSecs : Int := 0
  walNanos : UInt32 := 0
  deriving BEq

structure LogState where
  /-- How many rows are in storage. -/
  rows : Nat := 0
  objects : Array Obj := #[]
  sig : Sig := {}
  lastNewRows : Nat := 0
  deriving Inhabited

structure Mirror where
  url : String
  dataDir : System.FilePath
  state : Std.Mutex (Std.HashMap String LogState)

/-- A number with leading zeros, so that keys sort in order. -/
def pad (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (12 - s.length) '0') ++ s

def keyOf (file : String) (o : Obj) : String :=
  s!"v1/{file}/{pad o.first}-{pad o.count}.jsonl"

/-- Read a key back. Anything else in the bucket is not ours. -/
def parseKey (key : String) : Option (String × Obj) :=
  match key.splitOn "/" with
  | ["v1", file, name] =>
    match name.splitOn ".jsonl" with
    | [range, ""] =>
      match range.splitOn "-" with
      | [a, b] => do
        let first ← a.toNat?
        let count ← b.toNat?
        if isLog file then some (file, { first, count }) else none
      | _ => none
    | _ => none
  | _ => none

/-- Rows as the body of an object. Each is a JSON string, so any row fits on one line. -/
def encodeRows (rows : Array String) : String :=
  String.join (rows.toList.map fun r => (Json.str r).compress ++ "\n")

def decodeRows (body : String) : Except String (Array String) := do
  let mut out := #[]
  for line in body.splitOn "\n" do
    if !line.isEmpty then
      match ← Json.parse line with
      | .str s => out := out.push s
      | _ => throw "a line is not a string"
  return out

/-- The objects to read to get a whole log, in order, or the first gap. Each one read must carry the
log further, so an object inside one already chosen is skipped. -/
def plan (objects : Array Obj) : Except String (List Obj × Nat) := do
  let sorted := objects.qsort fun a b => a.first < b.first || (a.first == b.first && a.count > b.count)
  let mut next := 0
  let mut chosen : List Obj := []
  for o in sorted do
    if o.first > next then throw s!"rows {next} to {o.first - 1} are missing"
    if o.first + o.count > next then
      chosen := o :: chosen
      next := o.first + o.count
  return (chosen.reverse, next)

#guard keyOf "ABCDE.db" { first := 3, count := 4 } == "v1/ABCDE.db/000000000003-000000000004.jsonl"
#guard parseKey "v1/ABCDE.db/000000000003-000000000004.jsonl" == some ("ABCDE.db", { first := 3, count := 4 })
#guard (parseKey "v1/secret.txt/000000000003-000000000004.jsonl").isNone
#guard (decodeRows (encodeRows #["{\"t\":\"a\"}", "line\nbreak"])).toOption == some #["{\"t\":\"a\"}", "line\nbreak"]
-- A whole-log object wins over the small ones it covers, and overlap is fine.
#guard (plan #[{ first := 2, count := 1 }, { first := 0, count := 3 }, { first := 0, count := 2 }, { first := 3, count := 2 }]).toOption.map (·.2) == some 5
#guard ((plan #[{ first := 0, count := 3 }, { first := 0, count := 2 }]).toOption.map (·.1.length)) == some 1
-- A gap is an error, not a shorter game.
#guard (plan #[{ first := 0, count := 2 }, { first := 3, count := 2 }]).toOption.isNone

/-! ## Talking to storage -/

private def curlArgs (more : Array String) : Array String :=
  #["--fail", "--silent", "--show-error", "--max-time", "60"] ++ more

private def curlOk (args : Array String) : IO String := do
  let r ← IO.Process.output { cmd := "curl", args := curlArgs args }
  if r.exitCode != 0 then
    throw (IO.userError s!"curl: {r.stderr.trimAscii}")
  return r.stdout

private def put (m : Mirror) (key body : String) : IO Unit := do
  let child ← IO.Process.spawn
    { cmd := "curl", args := curlArgs #["-X", "PUT", "--data-binary", "@-", s!"{m.url}/o/{key}"]
      stdin := .piped, stdout := .null, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr body
  stdin.flush
  let _ := stdin
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then throw (IO.userError s!"curl: {err.trimAscii}")

private def del (m : Mirror) (key : String) : IO Unit :=
  discard <| curlOk #["-X", "DELETE", s!"{m.url}/o/{key}"]

/-- Every key in storage. -/
partial def listKeys (url : String) (cursor : Option String := none) (acc : Array String := #[]) :
    IO (Array String) := do
  let q := match cursor with
    | some c => s!"?cursor={c}"
    | none => ""
  let body ← curlOk #[s!"{url}/list{q}"]
  let j ← IO.ofExcept (Json.parse body)
  let keys : Array String ← IO.ofExcept (j.getObjValAs? (Array String) "keys")
  match jStr j "cursor" with
  | some c => listKeys url (some c) (acc ++ keys)
  | none => return acc ++ keys

/-! ## Restoring -/

/-- Fetch these objects into a folder, many at a time over one connection. -/
private def download (url : String) (dir : System.FilePath) (keys : Array String) : IO Unit := do
  if keys.isEmpty then return
  let mut cfg := ""
  for h : i in [0:keys.size] do
    cfg := cfg ++ s!"url = \"{url}/o/{keys[i]}\"\noutput = \"{(dir / toString i).toString}\"\n"
  let cfgPath := dir / "curl.cfg"
  IO.FS.writeFile cfgPath cfg
  discard <| curlOk #["--parallel", "--parallel-max", "16", "--config", cfgPath.toString]

/-- Bring the data folder up to what storage holds. Rows already on disk are kept, so this also works
on a disk that survived. Any problem throws: a server that lost a game must not look healthy. -/
def restore (url : String) (dataDir : System.FilePath) : IO (Mirror × Nat) := do
  let keys ← listKeys url
  let mut byFile : Std.HashMap String (Array Obj) := {}
  for k in keys do
    if let some (file, o) := parseKey k then
      byFile := byFile.insert file ((byFile.getD file #[]).push o)
  let mut wanted : Array (String × Obj) := #[]
  let mut states : Std.HashMap String LogState := {}
  for (file, objects) in byFile.toList do
    match plan objects with
    | .error why => throw (IO.userError s!"{file}: {why}")
    | .ok (chosen, rows) =>
      wanted := wanted ++ (chosen.map (file, ·)).toArray
      states := states.insert file { rows, objects }
  let dir := dataDir / ".restore"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  download url dir (wanted.map fun (f, o) => keyOf f o)
  let mut pending : Std.HashMap String (Array String) := {}
  for h : i in [0:wanted.size] do
    let (file, o) := wanted[i]
    let body ← try IO.FS.readFile (dir / toString i)
      catch err => throw (IO.userError s!"{keyOf file o} did not arrive: {err}")
    let rows ← match decodeRows body with
      | .ok rows => pure rows
      | .error why => throw (IO.userError s!"{keyOf file o} cannot be read: {why}")
    if rows.size != o.count then
      throw (IO.userError s!"{keyOf file o} has {rows.size} rows and should have {o.count}")
    let sofar := pending.getD file #[]
    -- Overlap: keep only the rows this object adds.
    pending := pending.insert file (sofar ++ rows.extract (sofar.size - o.first) rows.size)
  for (file, rows) in pending.toList do
    let log : EventLog.Log String ← EventLog.Log.open (dataDir / file)
    let onDisk ← log.count
    if onDisk < rows.size then
      discard <| log.appendAll (rows.extract onDisk rows.size)
  IO.FS.removeDirAll dir
  let state ← Std.Mutex.new states
  return ({ url, dataDir, state }, wanted.size)

/-! ## Copying -/

private def signature (path : System.FilePath) : IO Sig := do
  let main ← path.metadata
  let wal : System.FilePath := path.toString ++ "-wal"
  try
    let w ← wal.metadata
    return { size := main.byteSize, walSize := w.byteSize, walSecs := w.modified.sec, walNanos := w.modified.nsec }
  catch _ => return { size := main.byteSize }

/-- Write a log as one object, then delete the objects it replaces. -/
private def compact (m : Mirror) (file : String) (log : EventLog.Log String) (st : LogState) : IO LogState := do
  let rows ← log.readFrom 0
  let whole : Obj := { first := 0, count := rows.size }
  put m (keyOf file whole) (encodeRows rows)
  for o in st.objects do
    if o != whole then
      try del m (keyOf file o)
      catch err => IO.eprintln s!"mirror: {err}"
  return { st with rows := rows.size, objects := #[whole] }

/-- Too many objects means a slow restore, so a busy log is folded up now and then. -/
def maxObjects : Nat := 16
/-- A log with no new rows for this long is folded into one object. -/
def quietMs : Nat := 60000

/-- Copy what is new. `all` looks at every log, whatever its files say, and is for the last copy. -/
def flush (m : Mirror) (all : Bool := false) : IO Unit :=
  m.state.atomically do
    let now ← IO.monoMsNow
    for f in ← m.dataDir.readDir do
      if !isLog f.fileName then continue
      let states ← get
      let st := states.getD f.fileName {}
      let sig ← signature f.path
      let changed := all || !(sig == st.sig)
      let foldable := st.objects.size > 1 && (st.objects.size ≥ maxObjects || now - st.lastNewRows ≥ quietMs)
      if !changed && !foldable then continue
      let log : EventLog.Log String ← EventLog.Log.open f.path
      let mut st := st
      let total ← log.count
      if total > st.rows then
        let rows ← log.readFrom st.rows
        let o : Obj := { first := st.rows, count := rows.size }
        put m (keyOf f.fileName o) (encodeRows rows)
        st := { st with rows := st.rows + rows.size, objects := st.objects.push o, lastNewRows := now }
      st := { st with sig }
      if st.objects.size > 1 && (st.objects.size ≥ maxObjects || now - st.lastNewRows ≥ quietMs) then
        st ← compact m f.fileName log st
      modify (·.insert f.fileName st)

/-- The copying thread. If storage cannot be reached the server keeps playing, and says so in its log
once a minute. Nothing is lost while the disk lives, because the next copy starts where the last one
stopped. -/
partial def loop (m : Mirror) (intervalMs : Nat) (lastComplaint : Nat := 0) : IO Unit := do
  IO.sleep intervalMs.toUInt32
  try
    flush m
    loop m intervalMs lastComplaint
  catch err =>
    let now ← IO.monoMsNow
    let quiet := now - lastComplaint < 60000 && lastComplaint != 0
    if !quiet then
      IO.eprintln s!"mirror: storage cannot be reached, retrying: {err}"
    IO.sleep 4000
    loop m intervalMs (if quiet then lastComplaint else now)

end CharterServer.Mirror
