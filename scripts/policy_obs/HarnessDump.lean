import CharterRL.Obs
import Server.PreviewCheck
open Lean Charter CharterServer CharterServer.Bots CharterRL

/-- Play each game with a fixed rule (the k-th legal non-declare action) and print the observation at each decision. -/
def main : IO Unit := do
  for spec in gameSpecs do
    let .ok g := PreviewCheck.newTable spec 4 7 | IO.println "no table"; return
    let some s0 := g.state | return
    let G := g.spec.G
    let T := { Tables.ofSpec g.spec with declares := true }
    let ctx := Ctx.of G
    let st : Settings := { moveRows := false, preview := true, slotOrder := .game }
    let mut s : State G := cast (by rfl) s0
    for k in [0:80] do
      if s.phase == .ended then break
      let some p := s.currentSeat | break
      let ep := (Episode.make G .game 0).seat s.rules.pieces
      let d : Decision := .turn p
      let free := freeMap ctx s
      let reach := reachMap ctx s p
      let places := placeList ctx ep s p free reach
      let acts := (legal T ep places s d).filter fun (a, _) => !(actDeclare ≤ a && a < actPlace)
      let obs := observe T ep ctx st (template T ep G s.turnOrder.length false) s d places free reach none
      IO.println (s!"{spec.id} {k} " ++ " ".intercalate (obs.toList.map toString))
      let some (_, ev) := acts[(k * 7) % acts.length]? | break
      match Engine.step G s ev with
      | .ok s' => s := s'
      | .error e => IO.println s!"refused {e}"; break
