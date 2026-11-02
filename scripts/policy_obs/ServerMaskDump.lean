import Server.Policy.Bot
import Server.PreviewCheck
open Lean Charter CharterServer CharterServer.Bots CharterServer.Policy

/-- The server's side of `HarnessMaskDump.lean`: the same games by the same rule, with the policy's mask rules
`prune_declares` and `declare_once_per_turn` on and the ranked table of moves. -/
def main : IO Unit := do
  for spec in gameSpecs do
    let .ok g := PreviewCheck.newTable spec 4 7 | IO.println "no table"; return
    let some s0 := g.state | return
    let G := g.spec.G
    let mut s : State G := s0
    let mut lastTrade : Option (Nat × Nat × Res × Res) := none
    let mut declared : List (Nat × Nat × Res) := []
    for k in [0:120] do
      if s.phase == .ended then break
      let some p := s.currentSeat | break
      let undo := match lastTrade with
        | some (t, q, a, b) => if q == p && t == s.turnsTaken then some (b, a) else none
        | none => none
      let now := declared.filterMap fun (t, q, r) => if t == s.turnsTaken && q == p then some r else none
      let m : MaskRules := { moveRows := true, rankedMoves := true, prune := true, undo, declaredNow := now }
      let (obs, acts) := decisionFor g s p m
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
