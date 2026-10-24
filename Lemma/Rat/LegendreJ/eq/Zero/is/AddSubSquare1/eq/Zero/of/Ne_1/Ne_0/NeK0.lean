import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_LegendreJ
import Lemma.Int.P2MUtil
open ModularCurve


private lemma  legendreJ_eq_zero_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) : legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  rw [legendreJ, div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_right (pow_ne_zero _ h2)]
  exact pow_eq_zero_iff three_ne_zero

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_zero_iff.ModularCurve"
/--
[ModularCurve_legendreJ_eq_zero_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_legendreJ_eq_zero_iff.lean)
-/
@[path]
private lemma main
  [Field K]
  {t : K}
-- given
  (h0 : (2 : K) ≠ 0)
  (ht0 : t ≠ 0)
  (ht1 : t ≠ 1) :
-- imply
  legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 :=
-- proof
  legendreJ_eq_zero_iff' h0 ht0 ht1


-- created on 2026-10-23
