import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {x y : Fin n → ℝ}
-- given
  (h₀ : A.mulVec x = A.mulVec y)
  (h₁ : A.det ≠ 0) :
-- imply
  x = y :=
-- proof
  Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).2 (IsUnit.mk0 _ h₁)) h₀


-- created on 2020-08-22
-- updated on 2026-10-17
