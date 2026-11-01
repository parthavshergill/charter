import Lean
import Codec.Compound

/-!
# `deriving Codec`

For a non-parametric inductive type whose constructor fields are
non-dependent and do not mention the type itself, `deriving Codec` generates

* `T.codecToWire` / `T.codecOfWire` and a `Codec T` instance built with
  `Codec.ofEquiv` (or `Codec.ofPartial` for enums),
* a `LawfulCodec T` instance when every field type has one,
* a `CanonicalCodec T` instance when every field type has one.

The proofs are generated terms (`cases a <;> rfl` and a `match` with `rfl` per
case) that the kernel checks like any other proof; nothing is trusted.

Wire format:
* enum-like types (every constructor has no fields, at least two
  constructors): the constructor index as a `Nat` (one byte below 128
  constructors); other values are rejected.
* otherwise: each constructor's fields as a right-nested product (`Unit` if no
  fields), and the constructors arranged as a balanced tree of `Sum`s, so the
  tag costs `⌈log₂ k⌉` bytes for `k` constructors.

Not supported (the handler reports an error): type parameters or indices,
recursive or mutual types, dependent fields.
-/

namespace Codec.Derive

open Lean Elab Command Term Meta
open Lean.Parser.Term (matchAltExpr matchAlt)

/-- Right-nested product of the given types (`Unit` when empty). -/
private def prodType (ts : Array Term) : TermElabM Term := do
  if ts.isEmpty then return ← `(Unit)
  let mut acc := ts.back!
  for t in ts.pop.reverse do
    acc ← `($t × $acc)
  return acc

/-- Tuple term / pattern matching `prodType`. -/
private def tuple (xs : Array Ident) : TermElabM Term := do
  if xs.isEmpty then return ← `(())
  if xs.size = 1 then return xs[0]!
  let xsT : Array Term := xs.map (fun x => (x : Term))
  `(⟨$xsT,*⟩)

/-- Balanced `Sum` tree over the leaves; returns the type and, for each leaf,
a function wrapping a payload term into the right injections. -/
private partial def sumTree (leaves : Array Term) :
    TermElabM (Term × Array (Term → TermElabM Term)) := do
  if leaves.size = 1 then return (leaves[0]!, #[pure])
  let mid := leaves.size / 2
  let (l, lw) ← sumTree (leaves.extract 0 mid)
  let (r, rw) ← sumTree (leaves.extract mid leaves.size)
  let ty ← `(Sum $l $r)
  let lw' := lw.map fun w t => do `(Sum.inl $(← w t))
  let rw' := rw.map fun w t => do `(Sum.inr $(← w t))
  return (ty, lw' ++ rw')

private structure CtorData where
  name : Name
  fieldTypes : Array Expr
  deriving Inhabited

private def getCtors (declName : Name) : MetaM (Array CtorData) := do
  let some (.inductInfo iv) := (← getEnv).find? declName
    | throwError "deriving Codec: {declName} is not an inductive type"
  if iv.numParams ≠ 0 || iv.numIndices ≠ 0 then
    throwError "deriving Codec: {declName} has parameters or indices; write the instance with Codec.ofEquiv"
  if iv.isRec || iv.all.length ≠ 1 || iv.isNested then
    throwError "deriving Codec: {declName} is recursive, nested or mutual; write the instance by hand"
  if iv.ctors.isEmpty then
    throwError "deriving Codec: {declName} has no constructors"
  iv.ctors.toArray.mapM fun c => do
    let some (.ctorInfo ci) := (← getEnv).find? c | throwError "unknown constructor {c}"
    forallTelescopeReducing ci.type fun xs _ => do
      let tys ← xs.mapM fun x => do
        let t ← inferType x
        if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "deriving Codec: constructor {c} has a dependent field"
        if t.getUsedConstants.contains declName then
          throwError "deriving Codec: constructor {c} mentions {declName}"
        return t
      return { name := c, fieldTypes := tys }

private def hasInst (cls : Name) (t : Expr) : MetaM Bool := do
  let codecInst ← synthInstance? (mkApp (mkConst ``Codec) t)
  match codecInst with
  | none => return false
  | some ci => return (← synthInstance? (mkApp2 (mkConst cls) t ci)).isSome

private def delabType (t : Expr) : MetaM Term :=
  withOptions (fun o => o.setBool `pp.fullNames true |>.setBool `pp.universes false) do
    PrettyPrinter.delab t

private def mkCmds (declName : Name) : TermElabM (Array Command) := do
  let ctors ← getCtors declName
  let root (n : Name) : Ident := mkIdent (`_root_ ++ n)
  let T := root declName
  let toW := root (declName ++ `codecToWire)
  let ofW := root (declName ++ `codecOfWire)
  let allFieldTypes := ctors.flatMap (·.fieldTypes)
  for t in allFieldTypes do
    unless (← synthInstance? (mkApp (mkConst ``Codec) t)).isSome do
      throwError "deriving Codec: no Codec instance for field type {t}"
  let lawful ← allFieldTypes.allM fun t => hasInst ``LawfulCodec t
  let canonical ← allFieldTypes.allM fun t => hasInst ``CanonicalCodec t
  let ctorId (c : Name) : Ident := root c
  if ctors.size ≥ 2 && ctors.all (·.fieldTypes.isEmpty) then
    -- Enum: constructor index as Nat.
    let toAlts ← ctors.mapIdxM fun i c =>
      `(matchAltExpr| | $(ctorId c.name):ident => $(quote i))
    let ofAlts ← ctors.mapIdxM fun i c =>
      `(matchAltExpr| | $(quote i) => some $(ctorId c.name):ident)
    let ofAlts := ofAlts.push (← `(matchAltExpr| | _ => none))
    let mut cmds := #[
      ← `(command| def $toW : $T → Nat := fun x => match x with $toAlts:matchAlt*),
      ← `(command| def $ofW : Nat → Option $T := fun n => match n with $ofAlts:matchAlt*),
      ← `(command| instance : Codec $T := Codec.ofPartial $toW $ofW),
      ← `(command| instance : LawfulCodec $T :=
            Codec.ofPartial_lawful $toW $ofW (fun a => by cases a <;> rfl))]
    cmds := cmds.push (← `(command| instance : CanonicalCodec $T :=
        Codec.ofPartial_canonical $toW $ofW (fun a b h => by
          simp only [$ofW:ident] at h
          split at h <;> first | (cases h; rfl) | cases h)))
    return cmds
  -- General: balanced Sum of products.
  let leaves ← ctors.mapM fun c => do prodType (← c.fieldTypes.mapM fun t => liftM (delabType t))
  let (wire, wraps) ← sumTree leaves
  let mut toAlts := #[]
  let mut ofAlts := #[]
  let mut canAlts := #[]
  for i in [0:ctors.size] do
    let c := ctors[i]!
    let xs : Array Ident := (Array.range c.fieldTypes.size).map fun j => mkIdent (Name.mkSimple s!"x{j}")
    let tup ← tuple xs
    let wrapped ← wraps[i]! tup
    let xsT : Array Term := xs.map (fun x => (x : Term))
    let app ← `(@$(ctorId c.name):ident $xsT*)
    toAlts := toAlts.push (← `(matchAltExpr| | $app => $wrapped))
    ofAlts := ofAlts.push (← `(matchAltExpr| | $wrapped => $app))
    canAlts := canAlts.push (← `(matchAltExpr| | $wrapped => rfl))
  let mut cmds := #[
    ← `(command| def $toW : $T → $wire := fun x => match x with $toAlts:matchAlt*),
    ← `(command| def $ofW : $wire → $T := fun w => match w with $ofAlts:matchAlt*),
    ← `(command| instance : Codec $T := Codec.ofEquiv $toW $ofW)]
  if lawful then
    cmds := cmds.push (← `(command| instance : LawfulCodec $T :=
        Codec.ofEquiv_lawful $toW $ofW (fun a => by cases a <;> rfl)))
  if canonical then
    cmds := cmds.push (← `(command| instance : CanonicalCodec $T :=
        Codec.ofEquiv_canonical $toW $ofW (fun w => match w with $canAlts:matchAlt*)))
  return cmds

def mkCodecHandler (declNames : Array Name) : CommandElabM Bool := do
  unless (← declNames.allM fun n => return (← getEnv).isConstructor n || ((← getEnv).find? n matches some (.inductInfo _))) do
    return false
  for n in declNames do
    let cmds ← liftTermElabM (mkCmds n)
    cmds.forM elabCommand
  return true

initialize registerDerivingHandler ``Codec mkCodecHandler

end Codec.Derive
