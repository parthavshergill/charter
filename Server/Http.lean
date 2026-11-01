import Std.Http
import Lean.Data.Json
import Server.Util

/-! HTTP helpers on top of `Std.Http`: responses, static files, MIME types. -/

namespace CharterServer
open Std Async Std.Http Lean

abbrev Req := Std.Http.Request Std.Http.Body.Stream
abbrev Resp := Std.Http.Response Std.Http.Body.Any

/-- A request header's value. -/
def headerOf (req : Req) (name : String) : Option String := do
  let n ← Header.Name.ofString? name
  let v ← req.line.headers.get? n
  return v.value

/-- The type of a scene stream. The bytes are not protobuf. This is the one type for binary data that
Cloudflare compresses on the way out, and a scene shrinks to a seventh or so. -/
def sceneType : String := "application/x-protobuf"

def respond (status : Status) (ctype : String) (body : ByteArray)
    (headers : List (String × String) := []) (cache : String := "no-store") : Async Resp := do
  let mut b := Response.new |>.status status |>.header! "Content-Type" ctype
    |>.header! "Cache-Control" cache
  for (k, v) in headers do
    b := b.header! k v
  let r ← b.fromBytes body
  return { r with body := Body.Any.ofBody r.body }

def respondJson (j : Json) (status : Status := .ok) : Async Resp :=
  respond status "application/json; charset=utf-8" j.compress.toUTF8

def respondErr (msg : String) (status : Status := .badRequest) : Async Resp :=
  respondJson (errJson msg) status

def mimeOf (path : String) : String :=
  let ext := (path.splitOn ".").getLast!
  match ext with
  | "html" => "text/html; charset=utf-8"
  | "js" | "mjs" => "text/javascript; charset=utf-8"
  | "css" => "text/css; charset=utf-8"
  | "json" => "application/json"
  | "svg" => "image/svg+xml"
  | "png" => "image/png"
  | "jpg" | "jpeg" => "image/jpeg"
  | "woff2" => "font/woff2"
  | "ico" => "image/x-icon"
  | "bin" => "application/octet-stream"
  | "wasm" => "application/wasm"
  | "txt" => "text/plain; charset=utf-8"
  | _ => "application/octet-stream"

/-- The value a client sent, without the mark `W/` that a cache in front of this server adds when it
compresses a response. Comparing the rest is what `If-None-Match` asks for. -/
def clientHasTag (req : Req) (tag : String) : Bool :=
  match headerOf req "if-none-match" with
  | none => false
  | some v => (v.splitOn ",").any fun t =>
      let t := t.trimAscii.toString
      t == "*" || t == tag || t == "W/" ++ tag

/-- A hash as 16 hex digits. -/
def hexOf (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The name of this set of web files, made from what they hold. Two servers with the same files give
the same name, so a restart keeps every browser's copy good. A change to any file gives a new name. -/
def hashWebFiles (root : System.FilePath) : IO String := do
  let files ← root.walkDir
  let mut named : Array (String × ByteArray) := #[]
  for f in files do
    if !(← f.isDir) then
      named := named.push (f.toString, ← IO.FS.readBinFile f)
  let sorted := named.qsort fun a b => a.1 < b.1
  return hexOf (sorted.foldl (fun h (n, b) => mixHash (mixHash h (hash n)) (hash b)) 7)

initialize webBuildRef : IO.Ref (Nat × String) ← IO.mkRef (0, "")

/-- The name of the web files, worked out at most every 2 seconds: a page load asks for it many times.
A server's files do not change, and this short wait is all that someone editing them can notice. -/
def webBuildOf (root : System.FilePath) : IO String := do
  let now ← IO.monoMsNow
  let (at_, name) ← webBuildRef.get
  if !name.isEmpty && now - at_ < 2000 then return name
  let fresh ← hashWebFiles root
  webBuildRef.set (now, fresh)
  return fresh

/-- What index.html says in place of the build's name. -/
def buildMark : String := "BUILD"

/-- The page. It is asked for again on each visit, and it is short. Its `<base>` names this build, so
every file it loads, and every file those load, comes from one build's folder. -/
def serveIndex (req : Req) (root : System.FilePath) : Async Resp := do
  let build ← webBuildOf root
  let tag := s!"\"{build}\""
  let headers := [("ETag", tag)]
  if clientHasTag req tag then
    return ← respond .notModified "text/html; charset=utf-8" .empty headers "no-cache"
  let page ← IO.FS.readFile (root / "index.html")
  respond .ok "text/html; charset=utf-8" (page.replace buildMark build).toUTF8 headers "no-cache"

/-- A file for the decoded path segments, or none. Rejects `..`, and a segment that starts with a dot. -/
def webFile? (root : System.FilePath) (segs : List String) : IO (Option System.FilePath) := do
  if segs.isEmpty || segs.any (fun s => s == ".." || s.startsWith ".") then return none
  let path := segs.foldl (· / ·) root
  if (← path.pathExists) && !(← path.isDir) then return some path
  return none

/-- A file of one build, at `/v/<build>/<path>`. Its address names its contents, so a browser can keep it
for good and need not ask again. A build that this server does not have gets a plain "not found", never
another build's file under its name: that is what stops a page from mixing old files with new ones. The
page reloads when this happens. -/
def serveBuild (root : System.FilePath) (build : String) (segs : List String) : Async Resp := do
  if build != (← webBuildOf root) then
    return ← respondErr "that version of the page has been replaced" .notFound
  match ← webFile? root segs with
  | none => respondErr "not found" .notFound
  | some path =>
    respond .ok (mimeOf path.toString) (← IO.FS.readBinFile path) [] "public, max-age=31536000, immutable"

/-- A file at its plain address, which scripts and tools use. A browser keeps it, and asks each time
whether it has changed. -/
def serveStatic (req : Req) (root : System.FilePath) (segs : List String) : Async Resp := do
  match segs with
  | [] | [""] | ["index.html"] => serveIndex req root
  | _ =>
    match ← webFile? root segs with
    | none => respondErr s!"not found: {String.intercalate "/" segs}" .notFound
    | some path =>
      let body ← IO.FS.readBinFile path
      let tag := s!"\"{hexOf (hash body)}\""
      let mime := mimeOf path.toString
      if clientHasTag req tag then
        respond .notModified mime .empty [("ETag", tag)] "no-cache"
      else
        respond .ok mime body [("ETag", tag)] "no-cache"

/-- Serve a mesh file by its name, which is its hash. A hash names its contents for good, so a browser
or a cache in front of this server can keep the file for ever. To move the files to other storage, send
these requests there instead: the player knows only this path. -/
def serveMeshFile (root : System.FilePath) (name : String) (folderOf : String → Option String) : Async Resp := do
  let hash := (name.dropEnd 5).toString
  let hex := hash.length == 64 && hash.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  match (if hex && name.endsWith ".mesh" then folderOf hash else none) with
  | none => respondErr "not found" .notFound
  | some folder =>
    let path := root / folder / name
    if ← path.pathExists then
      respond .ok "application/octet-stream" (← IO.FS.readBinFile path) [] "public, max-age=31536000, immutable"
    else respondErr "not found" .notFound

end CharterServer
