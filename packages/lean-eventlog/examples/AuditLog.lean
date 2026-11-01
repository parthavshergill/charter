import EventLog

/-! Second use case: an append-only audit log for a web app's admin actions.

Every privileged action is appended before it takes effect. The current access-control view
(who holds which role, failed-login counters) is a fold over the log, resumed from the latest
checkpoint. Usage: `lake exe audit_log [path.db]` (default: a temporary directory). -/

open EventLog

inductive Action where
  | login (user : String)
  | loginFailed (user : String)
  | grantRole (admin user role : String)
  | revokeRole (admin user role : String)
  | deleteRecord (admin : String) (id : Nat)
deriving Repr, DecidableEq

namespace Action

/-- Wire form: (tag, strings, number). -/
def toWire : Action → Nat × List String × Nat
  | login u => (0, [u], 0)
  | loginFailed u => (1, [u], 0)
  | grantRole a u r => (2, [a, u, r], 0)
  | revokeRole a u r => (3, [a, u, r], 0)
  | deleteRecord a n => (4, [a], n)

def ofWire : Nat × List String × Nat → Option Action
  | (0, [u], _) => some (login u)
  | (1, [u], _) => some (loginFailed u)
  | (2, [a, u, r], _) => some (grantRole a u r)
  | (3, [a, u, r], _) => some (revokeRole a u r)
  | (4, [a], n) => some (deleteRecord a n)
  | _ => none

instance : Codec Action := Codec.ofPartial toWire ofWire
instance : LawfulCodec Action :=
  Codec.ofPartial_lawful toWire ofWire (fun a => by cases a <;> rfl)

def describe : Action → String
  | login u => s!"{u} logged in"
  | loginFailed u => s!"failed login for {u}"
  | grantRole a u r => s!"{a} granted {r} to {u}"
  | revokeRole a u r => s!"{a} revoked {r} from {u}"
  | deleteRecord a n => s!"{a} deleted record #{n}"

end Action

/-- Access-control view: (user, role) pairs and failed-login counters. -/
structure View where
  roles : List (String × String) := []
  failed : List (String × Nat) := []
deriving Repr, Inhabited, BEq

instance : Codec View :=
  Codec.ofEquiv (fun v => (v.roles, v.failed)) (fun p => ⟨p.1, p.2⟩)

def bump (xs : List (String × Nat)) (u : String) : List (String × Nat) :=
  match xs.find? (·.1 == u) with
  | some (_, n) => (u, n + 1) :: xs.filter (·.1 != u)
  | none => (u, 1) :: xs

def View.step (v : View) : Action → View
  | .login u => { v with failed := v.failed.filter (·.1 != u) }
  | .loginFailed u => { v with failed := bump v.failed u }
  | .grantRole _ u r => if v.roles.contains (u, r) then v else { v with roles := v.roles ++ [(u, r)] }
  | .revokeRole _ u r => { v with roles := v.roles.filter (· != (u, r)) }
  | .deleteRecord _ _ => v

def run (path : System.FilePath) : IO Unit := do
  let log : Log Action ← Log.open path
  let day1 : Array Action := #[
    .grantRole "root" "alice" "admin",
    .login "alice",
    .loginFailed "mallory", .loginFailed "mallory",
    .grantRole "alice" "bob" "editor"]
  discard <| log.appendAll day1
  let cp ← log.checkpoint View.step {}
  IO.println s!"checkpoint at seq {cp.seq}"
  for a in #[Action.loginFailed "mallory", .deleteRecord "bob" 42, .revokeRole "alice" "bob" "editor"] do
    let seq ← log.append a
    IO.println s!"  #{seq}: {a.describe}"
  let v ← log.replay View.step {}
  IO.println s!"roles now: {v.roles}"
  IO.println s!"failed logins: {v.failed}"
  -- the snapshot shortcut agrees with a full fold of the log (replay_eq_fold, checked here at runtime)
  let full := (← log.toPure).state View.step {}
  IO.println s!"replay from checkpoint == full fold: {v == full}"
  IO.println "history of bob:"
  for a in ← log.readFrom 0 do
    let mentions := match a with
      | .grantRole _ u _ | .revokeRole _ u _ => u == "bob"
      | .deleteRecord admin _ => admin == "bob"
      | _ => false
    if mentions then IO.println s!"  {a.describe}"

def main (args : List String) : IO Unit := do
  match args with
  | p :: _ => run p
  | [] => IO.FS.withTempDir fun dir => run (dir / "audit.db")
