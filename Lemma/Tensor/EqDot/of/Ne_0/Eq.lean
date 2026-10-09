import sympy.sets.sets
import sympy.Basic
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {a b : Fin n → ℝ}
-- given
  (_h₀ : A.det ≠ 0)
  (h₁ : a ᵥ* A = b) :
-- imply
  a ᵥ* A ᵥ* A⁻¹ = b ᵥ* A⁻¹ := by
-- proof
  rw [h₁]


-- created on 2020-02-12
