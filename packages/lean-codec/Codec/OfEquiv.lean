import Codec.Basic

/-!
# Building codecs from other codecs

* `Codec.ofPartial f g` : encode `α` through `f : α → β`, decode through a
  partial inverse `g : β → Option α`. Lawful when `g (f a) = some a`;
  canonical when additionally `g b = some a → f a = b` and `β` is canonical.
* `Codec.ofEquiv f g` : the total special case with `g (f a) = a`.

Use them like this:
```
instance : Codec Color := Codec.ofEquiv Color.toNat Color.ofNat
instance : LawfulCodec Color := Codec.ofEquiv_lawful Color.toNat Color.ofNat Color.ofNat_toNat
```
-/

namespace Codec

variable {α β : Type}

/-- Codec for `α` via `f : α → β` and a partial inverse `g`. -/
@[instance_reducible] def ofPartial [Codec β] (f : α → β) (g : β → Option α) : Codec α where
  encode a := encode (f a)
  decodeFrom bs :=
    match decodeFrom (α := β) bs with
    | some (b, r) =>
      match g b with
      | some a => some (a, r)
      | none => none
    | none => none

/-- Codec for `α` via `f : α → β` and a total left inverse `g`. -/
@[instance_reducible] def ofEquiv [Codec β] (f : α → β) (g : β → α) : Codec α :=
  ofPartial f (fun b => some (g b))

theorem ofPartial_lawful [Codec β] [LawfulCodec β] (f : α → β) (g : β → Option α)
    (h : ∀ a, g (f a) = some a) : @LawfulCodec α (ofPartial f g) :=
  @LawfulCodec.mk α (ofPartial f g) fun a rest => by
    show (match decodeFrom (α := β) (encode (f a) ++ rest) with
      | some (b, r) => match g b with | some a => some (a, r) | none => none
      | none => none) = some (a, rest)
    rw [Codec.decodeFrom_encode]; simp [h]

theorem ofPartial_canonical [Codec β] [CanonicalCodec β] (f : α → β) (g : β → Option α)
    (h : ∀ a b, g b = some a → f a = b) : @CanonicalCodec α (ofPartial f g) :=
  @CanonicalCodec.mk α (ofPartial f g) fun bs a rest hd => by
    change (match decodeFrom (α := β) bs with
      | some (b, r) => match g b with | some a => some (a, r) | none => none
      | none => none) = some (a, rest) at hd
    show bs = encode (f a) ++ rest
    split at hd
    · rename_i b r hb
      split at hd
      · rename_i a' ha
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        rw [CanonicalCodec.encode_decode _ _ _ hb, h _ _ ha]
      · cases hd
    · cases hd

theorem ofEquiv_lawful [Codec β] [LawfulCodec β] (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : @LawfulCodec α (ofEquiv f g) :=
  ofPartial_lawful f _ (fun a => by simp [h])

theorem ofEquiv_canonical [Codec β] [CanonicalCodec β] (f : α → β) (g : β → α)
    (h : ∀ b, f (g b) = b) : @CanonicalCodec α (ofEquiv f g) :=
  ofPartial_canonical f _ (fun a b hb => by cases hb; exact h b)

end Codec
