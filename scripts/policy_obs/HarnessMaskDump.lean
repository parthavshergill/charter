import CharterRL.Obs
import Server.PreviewCheck
open Lean Charter CharterServer CharterServer.Bots CharterRL

/-- Play each game by a fixed rule over every legal action (declarations and trades included), with
`prune_declares` and `declare_once_per_turn` on, and print the mask and the observation at each decision. -/
def main : IO Unit := do
  for spec in gameSpecs do
    let .ok g := PreviewCheck.newTable spec 4 7 | IO.println "no table"; return
    let some s0 := g.state | return
    let G := g.spec.G
    let T := { Tables.ofSpec g.spec with declares := true }
    let ctx := Ctx.of G
    let st : Settings := { moveRows := true, preview := true, slotOrder := .game, declareAlways := true,
                           pruneDeclares := true, declareOncePerTurn := true }
    let mut s : State G := cast (by rfl) s0
    let mut lastTrade : Option (Nat × Nat × Res × Res) := none
    let mut declared : List (Nat × Nat × Res) := []
    for k in [0:120] do
      if s.phase == .ended then break
      let some p := s.currentSeat | break
      let ep := (Episode.make G .game 0).seat s.rules.pieces
      let d : Decision := .turn p
      let free := freeMap ctx s
      let reach := reachMap ctx s p
      let places := placeList ctx ep s p free reach
      let undo := match lastTrade with
        | some (t, q, a, b) => if q == p && t == s.turnsTaken then some (b, a) else none
        | none => none
      let now := declared.filterMap fun (t, q, r) => if t == s.turnsTaken && q == p then some r else none
      let acts := legal T ep places s d undo true now
      let obs := observe T ep ctx st (template T ep G s.turnOrder.length true) s d places free reach none undo now
      IO.println (s!"{spec.id} {k} mask " ++ " ".intercalate (acts.map (toString ·.1)))
      IO.println (s!"{spec.id} {k} " ++ " ".intercalate (obs.toList.map toString))
      let some (_, ev) := acts[(k * 7) % acts.length]? | break
      match ev with
      | .move q (.bankTrade a b) => lastTrade := some (s.turnsTaken, q, a, b)
      | .move q (.declare r _) => declared := (s.turnsTaken, q, r) :: declared
      | _ => pure ()
      match Engine.step G s ev with
      | .ok s' => s := s'
      | .error e => IO.println s!"refused {e}"; break
