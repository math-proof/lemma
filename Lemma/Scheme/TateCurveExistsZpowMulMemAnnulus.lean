import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma nnnorm_lt_one_iff_norm {K : Type*} {x : K} [NontriviallyNormedField K] : nnnorm x < 1 ↔ ‖x‖ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
private lemma exists_zpow_mul_norm_Ioc {K : Type*} {q u : K} [NontriviallyNormedField K] (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) : ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _
  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc
        _ = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc
      _ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      rw [mul_comm]
      apply hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc
      _ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey
private lemma exists_zpow_mul_mem_annulus {K : Type*} {q u : K} [NontriviallyNormedField K] (hq0 : q ≠ 0) (hq : nnnorm q < 1) (hu0 : u ≠ 0) : ∃ n : ℤ, nnnorm (q * (q ^ n * u)) < 1 ∧ nnnorm (q * (q ^ n * u)⁻¹) < 1 := by
  have hqR : ‖q‖ < 1 := nnnorm_lt_one_iff_norm.mp hq
  obtain ⟨n, h1, h2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hu0
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hv_pos : (0 : ℝ) < ‖q ^ n * u‖ := lt_trans hq_pos h1
  refine ⟨n, nnnorm_lt_one_iff_norm.mpr ?_, nnnorm_lt_one_iff_norm.mpr ?_⟩
  ·
    rw [norm_mul]
    calc
      _ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h2 hq_pos.le
      _ = ‖q‖ := mul_one _
      _ < 1 := hqR
  ·
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hv_pos]
    apply h1
/--
[TateCurve_exists_zpow_mul_mem_annulus](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TateCurve_exists_zpow_mul_mem_annulus.lean)
-/
@[path]
private lemma main
  {q u : K} [NontriviallyNormedField K]
  (hq0 : q ≠ 0) (hq : nnnorm q < 1) (hu0 : u ≠ 0) :
  -- imply
  ∃ n : ℤ, nnnorm (q * (q ^ n * u)) < 1 ∧ nnnorm (q * (q ^ n * u)⁻¹) < 1 :=
  exists_zpow_mul_mem_annulus hq0 hq hu0


-- created on 2026-10-20
