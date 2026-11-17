module

public import Mathlib.Data.Finset.Basic
public import Theorem.Algebra.Power


public section

/-- Finite-support geometric weights: `γ ^ s` for `s : Finset ℕ`. Used with `⬝ᵥ` as
`∑ i ∈ s, γ^i * g i`. -/
structure FinsetPow (α : Type*) where
  base : α
  support : Finset ℕ

