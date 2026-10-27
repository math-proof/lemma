import Mathlib.Data.Finset.Basic
import Notation.Algebra.Power


/-- `γ ^ f` for an exponent sequence `f : ℕ → ℕ`: the sequence `k ↦ γ ^ f k`; e.g. the discount
weights `γ ^ (id : ℕ → ℕ) = fun k ↦ γ ^ k`. -/
instance Function.instHPowNatSeq {α : Type u} [HPow α Nat α] : HPow α (Nat → Nat) (Nat → α) where
  hPow γ f := fun k ↦ γ ^ f k

