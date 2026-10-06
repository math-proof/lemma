import Mathlib
import sympy.Basic

open PowerSeries

/--
[WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_exists_isUnit_discriminant_and_c4_cube_eq_mul_C_add_X_powerSeries.lean)
-/
@[main]
private lemma main
  [Field K]
  {a : K}
-- given
  (ha0 : a ≠ 0)
  (ha1728 : a ≠ 1728) :
-- imply
  ∃ E : WeierstrassCurve (PowerSeries K), IsUnit E.Δ ∧ E.c₄ ^ 3 = E.Δ * (PowerSeries.C a + PowerSeries.X) := by
-- proof
  have hj₀u : IsUnit (PowerSeries.C a + PowerSeries.X : PowerSeries K) := by
    refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
    simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
    exact ha0
  have hdu : IsUnit (PowerSeries.C a + PowerSeries.X - 1728 : PowerSeries K) := by
    refine PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr ?_)
    simp only [map_sub, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero, map_ofNat]
    exact sub_ne_zero.mpr ha1728
  obtain ⟨u, hrel⟩ : ∃ u : PowerSeries K, u * (PowerSeries.C a + PowerSeries.X - 1728) = 1 := by
    obtain ⟨d, hd⟩ := hdu
    exact ⟨↑d⁻¹, by rw [← hd, Units.inv_mul]⟩
  have huu : IsUnit u := ⟨⟨u, _, hrel, by rw [mul_comm]; exact hrel⟩, rfl⟩
  have hc₄ : (⟨1, 0, 0, -36 * u, -u⟩ : WeierstrassCurve (PowerSeries K)).c₄
      = (PowerSeries.C a + PowerSeries.X) * u := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    linear_combination (-1 : PowerSeries K) * hrel
  have hΔ : (⟨1, 0, 0, -36 * u, -u⟩ : WeierstrassCurve (PowerSeries K)).Δ
      = (PowerSeries.C a + PowerSeries.X) ^ 2 * u ^ 3 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination (-(u + u ^ 2 * (PowerSeries.C a + PowerSeries.X - 1728) + 3456 * u ^ 2)) * hrel
  refine ⟨⟨1, 0, 0, -36 * u, -u⟩, ?_, ?_⟩
  · rw [hΔ]; exact (hj₀u.pow 2).mul (huu.pow 3)
  · rw [hc₄, hΔ]; ring


-- created on 2026-10-05
