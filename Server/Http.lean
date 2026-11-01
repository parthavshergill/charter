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

/-- Serve a file under `root` for the decoded path segments. Rejects `..`. When the client
accepts it and `<file>.br` / `<file>.gz` exists, the precompressed file is sent with
`Content-Encoding` (used for the wasm engine). -/
def serveStatic (root : System.FilePath) (segs : List String) (acceptEnc : String := "") : Async Resp := do
  if segs.any (fun s => s == ".." || s.startsWith ".") then
    return ← respondErr "bad path" .forbidden
  let segs := if segs.isEmpty || segs == [""] then ["index.html"] else segs
  let path := segs.foldl (· / ·) root
  let path ← if (← path.isDir) then pure (path / "index.html") else pure path
  if ← path.pathExists then
    let mime := mimeOf path.toString
    let has (enc : String) : Bool := (acceptEnc.splitOn enc).length > 1
    let br : System.FilePath := path.toString ++ ".br"
    let gz : System.FilePath := path.toString ++ ".gz"
    if has "br" && (← br.pathExists) then
      return ← respond .ok mime (← IO.FS.readBinFile br) [("Content-Encoding", "br"), ("Vary", "Accept-Encoding")]
    if has "gzip" && (← gz.pathExists) then
      return ← respond .ok mime (← IO.FS.readBinFile gz) [("Content-Encoding", "gzip"), ("Vary", "Accept-Encoding")]
    respond .ok mime (← IO.FS.readBinFile path)
  else
    respondErr s!"not found: {String.intercalate "/" segs}" .notFound

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
