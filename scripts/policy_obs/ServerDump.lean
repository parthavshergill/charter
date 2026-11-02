import Server.Policy.Bot
import Server.PreviewCheck
open Lean Charter CharterServer CharterServer.Bots CharterServer.Policy

def main : IO Unit := do
  for spec in gameSpecs do
    let .ok g := PreviewCheck.newTable spec 4 7 | IO.println "no table"; return
    let some s0 := g.state | return
    let G := g.spec.G
    let mut s : State G := s0
    for k in [0:80] do
      if s.phase == .ended then break
      let some p := s.currentSeat | break
      let (obs, acts) := decisionFor g s p
      let acts := acts.filter fun (a, _) => !(actDeclare ≤ a && a < actPlace)
      IO.println (s!"{spec.id} {k} " ++ " ".intercalate (obs.toList.map toString))
      let some (_, ev) := acts[(k * 7) % acts.length]? | break
      match Engine.step G s ev with
      | .ok s' => s := s'
      | .error e => IO.println s!"refused {e}"; break
