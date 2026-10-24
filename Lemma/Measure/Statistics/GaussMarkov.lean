import Mathlib
import sympy.Basic
open Matrix


namespace MathlibExt.Probability.Statistics.GaussMarkov

/--
[gaussMarkov_covariance_minimality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/GaussMarkov.lean)
-/
@[path]
lemma gaussMarkov_covariance_minimality
  {m n : ℕ}
  {X : Matrix (Fin m) (Fin n) ℝ}
-- given
  (hX : IsUnit (Xᵀ * X)) :
-- imply
  let B := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-23
