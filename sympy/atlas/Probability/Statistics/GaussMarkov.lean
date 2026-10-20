/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/GaussMarkov.lean -/

import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Gauss–Markov covariance minimality

Authors: Muse Spark 1.3

In the unit-noise model with invertible `Xᵀ * X`, the least-squares matrix
`B = (Xᵀ * X)⁻¹ * Xᵀ` satisfies `B * X = 1`, and `A * Aᵀ - B * Bᵀ` is
positive semidefinite for every `A` with `A * X = 1`.
-/

namespace MathlibExt.Probability.Statistics.GaussMarkov

open Matrix

/--
In the unit-noise model with invertible `Xᵀ * X`, the least-squares matrix `B = (Xᵀ * X)⁻¹ * Xᵀ`
satisfies `B * X = 1` and `A * Aᵀ - B * Bᵀ` is `PosSemidef` for every `A` with `A * X = 1`.
Source: C. F. Gauss, *Theoria combinationis observationum erroribus minimis obnoxiae* (1823); A. C.
Aitken, “On Least Squares and Linear Combination of Observations,” *Proceedings of the Royal
Society of Edinburgh* 55 (1936), 42–48, DOI `10.1017/S0370164600014346`.
-/
theorem gaussMarkov_covariance_minimality
    {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ)
    (hX : IsUnit (Xᵀ * X)) :
    let B := (Xᵀ * X)⁻¹ * Xᵀ
    B * X = (1 : Matrix (Fin n) (Fin n) ℝ) ∧
      ∀ A : Matrix (Fin n) (Fin m) ℝ,
        A * X = (1 : Matrix (Fin n) (Fin n) ℝ) →
          (A * Aᵀ - B * Bᵀ).PosSemidef := by
  have hdet : IsUnit (Xᵀ * X).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hX
  have hBX : ((Xᵀ * X)⁻¹ * Xᵀ) * X = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]
  change ((Xᵀ * X)⁻¹ * Xᵀ) * X = 1 ∧ _
  refine ⟨hBX, fun A hA => ?_⟩
  have hDX : (A - (Xᵀ * X)⁻¹ * Xᵀ) * X = 0 := by
    rw [Matrix.sub_mul, hA, hBX, sub_self]
  have hBT : (((Xᵀ * X)⁻¹ * Xᵀ : Matrix (Fin n) (Fin m) ℝ))ᵀ
      = X * ((Xᵀ * X)⁻¹)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hDB : (A - (Xᵀ * X)⁻¹ * Xᵀ) * (((Xᵀ * X)⁻¹ * Xᵀ))ᵀ = 0 := by
    rw [hBT, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have hBD : ((Xᵀ * X)⁻¹ * Xᵀ) * (A - (Xᵀ * X)⁻¹ * Xᵀ)ᵀ = 0 := by
    have h := congrArg Matrix.transpose hDB
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] at h
  have hABT : A * (((Xᵀ * X)⁻¹ * Xᵀ))ᵀ
      = ((Xᵀ * X)⁻¹ * Xᵀ) * (((Xᵀ * X)⁻¹ * Xᵀ))ᵀ := by
    have hAeq : A = (A - (Xᵀ * X)⁻¹ * Xᵀ) + (Xᵀ * X)⁻¹ * Xᵀ :=
      (sub_add_cancel _ _).symm
    conv_lhs => rw [hAeq]
    rw [Matrix.add_mul, hDB, zero_add]
  have key : A * Aᵀ - ((Xᵀ * X)⁻¹ * Xᵀ) * (((Xᵀ * X)⁻¹ * Xᵀ))ᵀ
      = (A - (Xᵀ * X)⁻¹ * Xᵀ) * (A - (Xᵀ * X)⁻¹ * Xᵀ)ᵀ := by
    rw [Matrix.sub_mul, hBD, Matrix.transpose_sub, Matrix.mul_sub, hABT, sub_zero]
  rw [key]
  have hPSD := Matrix.posSemidef_self_mul_conjTranspose
    (A - (Xᵀ * X)⁻¹ * Xᵀ)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hPSD

end MathlibExt.Probability.Statistics.GaussMarkov
