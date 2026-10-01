import sympy.functions.elementary.complexes
import sympy.Basic
import Mathlib.Data.Matrix.Mul
open Complex
open scoped ComplexOrder


@[main]
private lemma positive_definite
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
  {j : Fin n}
-- given
  (h : ∀ x : Fin n → ℂ, x ≠ 0 → (fun i => ~(x i)) ⬝ᵥ A.mulVec x > 0) :
-- imply
  A j j > 0 := by
-- proof
  have h₁ := h (Pi.single j 1) fun h₀ => by simpa using congrFun h₀ j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h₁


-- created on 2026-09-27
