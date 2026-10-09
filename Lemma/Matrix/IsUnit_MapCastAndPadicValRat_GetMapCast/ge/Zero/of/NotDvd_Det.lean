import Mathlib
import sympy.Basic


/--
[Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det.lean)
-/
@[path]
private lemma main
  [Fintype m] [DecidableEq m]
  {p : ℕ} [Fact p.Prime]
  {M : Matrix m m ℤ}
-- given
  (hM : ¬ (p : ℤ) ∣ M.det) :
-- imply
  IsUnit (M.map (Int.cast : ℤ → ℚ)) ∧
      ∀ i j, 0 ≤ padicValRat p ((M.map (Int.cast : ℤ → ℚ))⁻¹ i j) := by
-- proof
  have hdet : (M.map (Int.cast : ℤ → ℚ)).det = (M.det : ℚ) := by
    have h := RingHom.map_det (Int.castRingHom ℚ) M
    rw [RingHom.mapMatrix_apply] at h
    simpa using h.symm
  have hdet0 : M.det ≠ 0 := fun h => hM (h ▸ dvd_zero _)
  have hQdet0 : (M.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [hdet]; exact_mod_cast hdet0
  have hunit : IsUnit (M.map (Int.cast : ℤ → ℚ)).det := isUnit_iff_ne_zero.mpr hQdet0
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).mpr hunit, fun i j => ?_⟩
  have hadj : (M.map (Int.cast : ℤ → ℚ)).adjugate = M.adjugate.map (Int.cast : ℤ → ℚ) := by
    have h := (Int.castRingHom ℚ).map_adjugate M
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    simpa using h.symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', hadj, Matrix.map_apply,
    hdet]
  by_cases hz : M.adjugate i j = 0
  · simp [hz]
  · rw [padicValRat.mul (inv_ne_zero (by exact_mod_cast hdet0)) (by exact_mod_cast hz),
      padicValRat.inv, padicValRat.of_int, padicValRat.of_int,
      padicValInt.eq_zero_of_not_dvd hM]
    simp


-- created on 2026-10-05
