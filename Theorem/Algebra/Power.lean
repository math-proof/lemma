module

public import Mathlib.Data.Finset.Basic

@[expose] public section

universe u

/-- `γ ^ f` for an exponent sequence `f : ℕ → ℕ`: the sequence `k ↦ γ ^ f k`; e.g. the discount
weights `γ ^ (id : ℕ → ℕ)` = `fun k ↦ γ ^ k`. -/
public instance Function.instHPowNatSeq {α : Type u} [HPow α Nat α] : HPow α (Nat → Nat) (Nat → α) where
  hPow γ f := fun k ↦ γ ^ f k

@[simp]
public theorem Function.hPow_apply {α : Type u} [HPow α Nat α] (γ : α) (f : Nat → Nat) (k : Nat) :
    (γ ^ f) k = γ ^ f k := rfl
