import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {A B : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h₀ : A.det ≠ 0)
  (h₁ : B.det ≠ 0)
  (h₂ : (A + B).det ≠ 0) :
-- imply
  A * (A + B)⁻¹ * B = (A⁻¹ + B⁻¹)⁻¹ := by
-- proof
  have e1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr h₁)
  have e2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr h₀)
  have e3 : (A + B)⁻¹ * (A + B) = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h₂)
  symm
  apply Matrix.inv_eq_left_inv
  calc A * (A + B)⁻¹ * B * (A⁻¹ + B⁻¹) = A * ((A + B)⁻¹ * (A + B)) * A⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, e1, e2, Matrix.mul_one]
        abel
    _ = 1 := by rw [e3, Matrix.mul_one, e2]


-- created on 2023-05-01
