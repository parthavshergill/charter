import EventLog

/-! Build-time checks of the pure model. -/

namespace EventLog.Tests
open EventLog

def sumStep (s : Nat) (e : Nat) : Nat := s + e

def lg : PureLog Nat := (PureLog.empty.appendAll #[3, 1, 4, 1, 5, 9, 2, 6])

#guard lg.count == 8
#guard lg.readFrom 0 == #[3, 1, 4, 1, 5, 9, 2, 6]
#guard lg.readFrom 5 == #[9, 2, 6]
#guard lg.readFrom 8 == #[]
#guard lg.readFrom 20 == #[]
#guard lg.state sumStep 0 == 31
#guard (lg.snapshotAt sumStep 0 3) == ⟨3, 8⟩
#guard (lg.snapshotAt sumStep 0 100) == ⟨8, 31⟩
#guard (List.range 12).all fun k => lg.replayFrom sumStep (lg.snapshotAt sumStep 0 k) == 31
-- order matters for non-commutative steps
#guard (PureLog.empty.appendAll #["a", "b", "c"]).state (· ++ ·) "" == "abc"
#guard ((PureLog.empty.appendAll #["a", "b"]).append "c").readFrom 1 == #["b", "c"]

end EventLog.Tests
