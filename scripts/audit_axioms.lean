import Lean
open Lean

/-!
# Which axioms the theorems rest on

This does what `#print axioms` does, for every theorem in the project. It prints one line for each
promise in the constitution's files, and one for each statement about the parser. It checks every theorem
in a `Charter` module, including the proofs and the tests, and every theorem in `Server.ParserProof` and
`Server.ParserFacts`. It exits with an error if anything they rest on is an axiom outside the allowed list,
or if a statement about the parser is missing.

Run it with `make audit`, or:

    lake env lean --run scripts/audit_axioms.lean
-/

/-- The only axioms a theorem may use. `sorry` shows up as `sorryAx`, which is not on this list. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module with the statements about the parser. -/
def parserFacts : Name := `Server.ParserFacts

/-- The two statements about the parser. -/
def parserStatements : List Name := [`Charter.Rules.nothing_gets_ignored, `Charter.Rules.only_real_resources]

/-- This module's theorems are checked. -/
def isChecked (m : Name) : Bool := (`Charter).isPrefixOf m || m == parserFacts || m == `Server.ParserProof

/-- This theorem is one a reader of the constitution sees, or a statement about the parser. -/
def isShown (m n : Name) : Bool :=
  (m == `Charter.Constitution || m == `Charter.Constitution.Supporting ||
    m == `Charter.Constitution.Examples || m == `Charter.Proofs.IslandWitness || m == parserFacts) &&
  !n.isInternal && !isPrivateName n &&
  match n with
  | .str _ s => !s.startsWith "eq_" && s != "induct" && s != "mutual_induct"
  | _ => true

/-- The axioms each constant rests on, for each constant visited so far. -/
abbrev Seen := NameMap NameSet

/-- The constants this one's type and body use. -/
def usesOf (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo d => d.type.getUsedConstants ++ d.value.getUsedConstants
  | .thmInfo d => d.type.getUsedConstants ++ d.value.getUsedConstants
  | .opaqueInfo d => d.type.getUsedConstants ++ d.value.getUsedConstants
  | .inductInfo d => d.type.getUsedConstants ++ d.ctors.toArray
  | ci => ci.type.getUsedConstants

/-- The axioms `c` rests on. A loop between a type and its constructors stops at the first visit. So
this can leave an axiom out of one constant's own list, but `main` also looks at every axiom visited,
so it cannot miss one. -/
partial def axiomsOf (env : Environment) (c : Name) : StateM Seen NameSet := do
  if let some known := (← get).find? c then return known
  modify (·.insert c {})
  let some ci := env.find? c | return {}
  let mut found : NameSet := {}
  if let .axiomInfo _ := ci then found := found.insert c
  for u in usesOf ci do
    for a in (← axiomsOf env u) do
      found := found.insert a
  modify (·.insert c found)
  return found

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Charter }, { module := parserFacts }] {} (loadExts := true)
  for statement in parserStatements do
    unless env.contains statement do
      IO.eprintln s!"NOT FOUND: {statement}"
      return 1
  let mut seen : Seen := {}
  let mut total := 0
  let mut shown : Array String := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo _ := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless isChecked m do continue
    total := total + 1
    let (axioms, seen') := (axiomsOf env n).run seen
    seen := seen'
    if isShown m n then
      shown := shown.push s!"{n}: {axioms.toList}"
  for line in shown.qsort (· < ·) do
    IO.println line
  let visited := seen.toList.map (·.1)
  let everyAxiom := visited.filter fun c =>
    match env.find? c with
    | some (.axiomInfo _) => true
    | _ => false
  IO.println s!"Checked {total} theorems. Every axiom they rest on: {everyAxiom}"
  let wrong := everyAxiom.filter (!allowed.contains ·)
  if wrong.isEmpty then
    IO.println "All are allowed."
    return 0
  else
    IO.eprintln s!"NOT ALLOWED: {wrong}"
    return 1
