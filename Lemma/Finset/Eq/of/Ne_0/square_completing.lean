import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  (x b : Fin n → ℝ)
  (A : Matrix (Fin n) (Fin n) ℝ)
  (c : ℝ)
-- given
  (h₀ : (A + A.transpose).det ≠ 0) :
-- imply
  let S := A + A.transpose
  let h := Matrix.mulVec S⁻¹ b
  c + dotProduct b x + dotProduct x (Matrix.mulVec A x)
    = dotProduct (x + h) (Matrix.mulVec A (x + h))
      + (c - dotProduct h (Matrix.mulVec A h)) := by
-- proof
  intro S h
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr h₀
  have hSb : Matrix.mulVec S h = b := by
    simp [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hcross : dotProduct x (Matrix.mulVec A h) +
      dotProduct h (Matrix.mulVec A x) = dotProduct b x := by
    have hx : dotProduct x (Matrix.mulVec A h) = dotProduct (Matrix.mulVec A h) x :=
      dotProduct_comm _ _
    have hh : dotProduct h (Matrix.mulVec A x) = dotProduct (Matrix.mulVec A.transpose h) x := by
      rw [Matrix.dotProduct_mulVec]
      have hv : Matrix.vecMul h (Matrix.transpose (Matrix.transpose A)) =
          Matrix.mulVec A.transpose h :=
        Matrix.vecMul_transpose A.transpose h
      rw [Matrix.transpose_transpose] at hv
      rw [hv]
    rw [hx, hh, ← add_dotProduct, ← Matrix.add_mulVec, hSb]
  have hexp : dotProduct (x + h) (Matrix.mulVec A (x + h)) =
      dotProduct x (Matrix.mulVec A x) + dotProduct x (Matrix.mulVec A h) +
      dotProduct h (Matrix.mulVec A x) + dotProduct h (Matrix.mulVec A h) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    abel
  rw [hexp]
  calc
    _ = c + (dotProduct x (Matrix.mulVec A h) + dotProduct h (Matrix.mulVec A x)) +
      dotProduct x (Matrix.mulVec A x) := by
      rw [hcross]
    _ = dotProduct x (Matrix.mulVec A x) + dotProduct x (Matrix.mulVec A h) +
      dotProduct h (Matrix.mulVec A x) + dotProduct h (Matrix.mulVec A h) +
      (c - dotProduct h (Matrix.mulVec A h)) := by
      abel


-- created on 2026-10-11
-- updated on 2026-10-17
