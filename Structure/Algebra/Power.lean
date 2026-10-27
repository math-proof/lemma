import Mathlib.Data.Finset.Basic
import Theorem.Algebra.Power


/-- Finite-support geometric weights: `γ ^ s` for `s : Finset ℕ`. Used with `@` as
`∑ i ∈ s, γ^i * g i`. -/
structure FinsetPow (α : Type*) where
  base : α
  support : Finset ℕ

