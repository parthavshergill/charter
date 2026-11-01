import Charter.Proofs.Ledger
import Charter.Proofs.Limits
import Charter.Proofs.Turns
import Charter.Proofs.Exact
import Charter.Proofs.Majority
import Charter.Proofs.Deals
import Charter.Proofs.Winner
import Charter.Proofs.Prices
import Charter.Proofs.More

/-!
# What is true of every reachable state

`Inv` collects the facts proved by induction on the events of a game. `Main.lean` turns `Reachable`
into `Inv` with `Reachable.inv`.
-/

namespace Charter.Proofs

open Charter Charter.Engine

variable {G : GameDef}

/-- What every reachable state satisfies. -/
structure Inv (G : GameDef) (s : State G) : Prop where
  core : Core s
  limits : Limits s
  turns : TurnInv s
  events : EventInv s
  ids : IdInv s
  cover : Cover s
  deposits : DepositInv G s
  winner : WinnerInv G s
  prices : LawPrices G s
  kept : KeptInv s
  planned : PlannedInv s
  seat : CurrentSeatInv s

theorem Inv.start {G : GameDef} (hG : G.Valid) (seats : Nat) (serverSeed : UInt64)
    (nonces : List UInt64) (h1 : minSeats ≤ seats) (h2 : seats ≤ maxSeats) :
    Inv G (initialState G seats serverSeed nonces) :=
  ⟨Core.start G seats serverSeed nonces h1 h2, Limits.start hG seats serverSeed nonces h1 h2,
    TurnInv.start G seats serverSeed nonces h1, EventInv.start G seats serverSeed nonces,
    IdInv.start G seats serverSeed nonces,
    Cover.start G seats serverSeed nonces, DepositInv.start G seats serverSeed nonces,
    WinnerInv.start G seats serverSeed nonces, LawPrices.start hG seats serverSeed nonces h1 h2,
    KeptInv.start G seats serverSeed nonces, PlannedInv.start hG seats serverSeed nonces h1 h2,
    CurrentSeatInv.start G seats serverSeed nonces h1⟩

theorem Inv.step {s s' : State G} {e : Event} (hG : G.Valid) (hs : Inv G s)
    (h : Engine.step G s e = .ok s') : Inv G s' :=
  ⟨hs.core.step h, hs.limits.step h, hs.turns.step hG h,
    hs.events.step hs.turns hs.core.turnOrder_nodup h,
    hs.ids.step h, hs.cover.step hs.core hs.ids h,
    hs.deposits.step hs.core hs.ids h,
    hs.winner.step hs.turns (by
      obtain ⟨n, h2, _, ht⟩ := hs.core.seats
      have : 2 ≤ n := h2
      rw [ht]
      intro he
      have := congrArg List.length he
      simp at this
      omega) h,
    hs.prices.step h, hs.kept.step hs.ids h, hs.planned.step h,
    hs.seat.step (by
      obtain ⟨n, h2, _, ht⟩ := hs.core.seats
      have : 2 ≤ n := h2
      rw [ht, List.length_range]
      omega) h⟩

end Charter.Proofs
