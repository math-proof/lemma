import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[main]
private lemma main
  {n : ℕ}
  {A B C : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : A * B = C)
  (h₁ : IsUnit C.det) :
-- imply
  A = C * B⁻¹ := by
-- proof
  have hB : IsUnit B.det := by
    rw [← h₀, Matrix.det_mul] at h₁
    exact isUnit_of_mul_isUnit_right h₁
  rw [← h₀, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]


-- created on 2023-04-30
