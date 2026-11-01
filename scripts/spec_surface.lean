import Lean
open Lean

/-!
# The trusted surface of each promise

A theorem means what its statement says. The statement means what every definition it mentions means,
and so on through those definitions' bodies. This prints that list for each promise. The proof is
not followed, because the kernel checks it.

This is `#spec_surface` from `CLAUDE.md`, with three changes:

* It runs over the whole project, not one file.
* It stops at `Charter.Engine`. The engine is the code the theorems are about, so a reader does not
  need to trust its body. Each engine function a statement names is still listed.
* It leaves out what Lean generates: structure fields, `casesOn`, match helpers and the like.

Run it with:

    lake env lean --run scripts/spec_surface.lean [--list] [theorem ...]
-/

def commandments : List Name :=
  [`Charter.I_nothing_from_nothing, `Charter.II_one_law_for_all, `Charter.III_only_the_majority,
   `Charter.IV_promises_are_paid_up_front, `Charter.V_your_money_is_yours,
   `Charter.VI_every_deal_ends, `Charter.VII_prices_are_real,
   `Charter.VIII_nobody_controls_the_dice, `Charter.IX_cannot_stall_always_ends,
   `Charter.X_what_you_vote_on_is_what_runs]

def supporting : List Name :=
  [`Charter.the_winner_earned_it, `Charter.limits_hold, `Charter.every_other_event_is_exact,
   `Charter.proposals_are_accepted, `Charter.deals_can_start]

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).bind fun i => env.header.moduleNames[i.toNat]?

def isCharter (m : Name) : Bool := (`Charter).isPrefixOf m

def isEngine (m : Name) : Bool := m == `Charter.Engine || (`Charter.Engine).isPrefixOf m

/-- The constants this one's type and body mention. -/
def uses (env : Environment) (c : Name) : List Name :=
  match env.find? c with
  | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
  | some (.inductInfo d) => d.type.getUsedConstants.toList ++ d.ctors
  | some ci => ci.type.getUsedConstants.toList
  | none => []

/-- Follow `todo` through bodies, stopping at the engine and at anything outside Charter. -/
partial def follow (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | c :: rest =>
    if seen.contains c then follow env rest seen else
    let seen := seen.insert c
    match moduleOf env c with
    | some m =>
      if !isCharter m || isEngine m then follow env rest seen
      else follow env (uses env c ++ rest) seen
    | none => follow env rest seen

/-- A definition a person wrote, as opposed to something Lean generates from it. -/
def isWritten (env : Environment) (c : Name) : Bool :=
  let last := match c with
    | .str _ s => s
    | _ => ""
  (match moduleOf env c with
   | some m => isCharter m
   | none => false) &&
  (match env.find? c with
   | some (.defnInfo _) | some (.inductInfo _) | some (.opaqueInfo _) => true
   | _ => false) &&
  !c.isInternal && !Meta.isMatcherCore env c && !(env.isProjectionFn c) &&
  !isAuxRecursor env c && !isNoConfusion env c &&
  !["ctorIdx", "below", "brecOn", "casesOn", "recOn"].contains last &&
  !last.startsWith "below_" && !last.startsWith "brecOn_" &&
  !c.components.any (fun x => x.toString.startsWith "brecOn") &&
  !last.startsWith "instDecidableEq" && !last.startsWith "instRepr" && !last.startsWith "decEq"

def surfaceOf (env : Environment) (thm : Name) : List Name :=
  match env.find? thm with
  | some ci =>
    ((follow env ci.type.getUsedConstants.toList {}).toList.filter (isWritten env))
  | none => []

def sortNames (l : List Name) : List Name :=
  (l.toArray.qsort (fun a b => toString a < toString b)).toList

/-- Group names by the file that defines them, and print each group. -/
def printGroups (env : Environment) (names : List Name) (list : Bool) : IO Unit := do
  let mut groups : Std.HashMap Name (List Name) := {}
  for c in names do
    let m := (moduleOf env c).getD .anonymous
    groups := groups.insert m (c :: groups.getD m [])
  for (m, cs) in (groups.toList.toArray.qsort fun a b => toString a.1 < toString b.1) do
    IO.println s!"  {m}: {cs.length}"
    if list then
      IO.println s!"    {" ".intercalate ((sortNames cs).map fun c =>
        (c.replacePrefix `Charter .anonymous).toString)}"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Charter }] {} (loadExts := true)
  let list := args.contains "--list"
  let named := (args.filter (· != "--list")).map String.toName
  let theorems := if named.isEmpty then commandments ++ supporting else named
  let mut all : NameSet := {}
  for t in theorems do
    let s := surfaceOf env t
    IO.println s!"{t}: {s.length} definitions"
    if list then printGroups env s true
    for c in s do all := all.insert c
  IO.println s!"All of them together: {all.toList.length} definitions"
  printGroups env all.toList list
