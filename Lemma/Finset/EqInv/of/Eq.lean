import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[path]
private lemma main
  [CommRing α]
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) α}
-- given
  (h : A = B) :
-- imply
  A⁻¹ = B⁻¹ := by
-- proof
  rw [h]


-- created on 2020-02-11
