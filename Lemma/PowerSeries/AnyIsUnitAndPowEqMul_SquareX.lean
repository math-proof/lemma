import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [Field K]
private lemma isUnit_1728_sub_X_cube (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsUnit ((1728 : PowerSeries K) - PowerSeries.X ^ 3) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_sub, map_ofNat, map_pow, PowerSeries.constantCoeff_X]
  have hfac : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
  norm_num
  rw [hfac]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
private lemma isUnit_1728_add_X_sq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    IsUnit ((1728 : PowerSeries K) + PowerSeries.X ^ 2) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_add, map_ofNat, map_pow, PowerSeries.constantCoeff_X]
  have hfac : (1728 : K) = 2 ^ 6 * 3 ^ 3 := by norm_num
  norm_num
  rw [hfac]; exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
private lemma isUnit_const (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (a b : ℕ) :
    IsUnit ((2 : PowerSeries K) ^ a * 3 ^ b) := by
  refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
  simp only [map_mul, map_pow, map_ofNat]
  exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
/--
[WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_isUnit_discriminant_and_c6_sq_eq_mul_X_sq_powerSeries.lean)
-/
@[path]
private lemma main
    (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    ∃ E : WeierstrassCurve (PowerSeries K), IsUnit E.Δ ∧ E.c₆ ^ 2 = E.Δ * PowerSeries.X ^ 2 := by
  set u : PowerSeries K := 1728 + PowerSeries.X ^ 2 with hu
  let E : WeierstrassCurve (PowerSeries K) := ⟨0, 0, 0, -3 * u, 2 * PowerSeries.X * u⟩
  have hΔ : E.Δ = (2 ^ 12 * 3 ^ 6) * u ^ 2 := by
    simp only [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [hu]; ring
  have hc₆ : E.c₆ = -1728 * PowerSeries.X * u := by
    simp only [E, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]; ring
  refine ⟨E, ?_, ?_⟩
  · rw [hΔ]
    exact (isUnit_const K h2 h3 12 6).mul ((isUnit_1728_add_X_sq K h2 h3).pow 2)
  · rw [hc₆, hΔ]; ring

-- created on 2026-10-20
