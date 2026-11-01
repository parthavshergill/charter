import Lean.Data.Json
import Charter.Words
import Server.Util

/-!
# JSON for moves

The log's form of a move. It is in its own file so that the bot policy and the arena can use it without
the rest of `Server/Game.lean`.
-/

namespace CharterServer.Game
open Lean Charter

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
  | .declare r n => Json.mkObj [("t", "declare"), ("res", r), ("n", toJson n)]
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
  | "declare" => pure (.declare (← j.getObjValAs? String "res") (← j.getObjValAs? Nat "n"))
  | "endTurn" => pure .endTurn
  | t => throw s!"unknown move {t}"

end CharterServer.Game
