import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.ModularCurve_LegendreJ
import Lemma.Int.P2MUtil
open ModularCurve


private lemma  legendreJ_inv' {K : Type*} [Field K] (t : K) : legendreJ t⁻¹ = legendreJ t := by
  if ht : t = 0 then
    rw [ht, inv_zero]
  else
    have hi : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    have hu : (t⁻¹ : K) ≠ 0 := inv_ne_zero ht
    have e1 : (t⁻¹ ^ 2 - t⁻¹ + 1) ^ 3 = (t ^ 2 - t + 1) ^ 3 * t⁻¹ ^ 6 := by
      linear_combination (-t^5*t⁻¹^5 + 3*t^4*t⁻¹^5 - t^4*t⁻¹^4 - 6*t^3*t⁻¹^5 + 3*t^3*t⁻¹^4 - t^3*t⁻¹^3 + 7*t^2*t⁻¹^5 - 6*t^2*t⁻¹^4 + 3*t^2*t⁻¹^3 - t^2*t⁻¹^2 - 6*t*t⁻¹^5 + 7*t*t⁻¹^4 - 6*t*t⁻¹^3 + 3*t*t⁻¹^2 - t*t⁻¹ + 3*t⁻¹^5 - 6*t⁻¹^4 + 7*t⁻¹^3 - 6*t⁻¹^2 + 3*t⁻¹ - 1) * hi
    have e2 : t⁻¹ ^ 2 * (t⁻¹ - 1) ^ 2 = (t ^ 2 * (t - 1) ^ 2) * t⁻¹ ^ 6 := by
      linear_combination (-t^3*t⁻¹^5 + 2*t^2*t⁻¹^5 - t^2*t⁻¹^4 - t*t⁻¹^5 + 2*t*t⁻¹^4 - t*t⁻¹^3 - t⁻¹^4 + 2*t⁻¹^3 - t⁻¹^2) * hi
    simp only [legendreJ]
    rw [e1, e2, ← mul_assoc, mul_div_mul_right _ _ (pow_ne_zero 6 hu)]

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_inv.ModularCurve"
/--
[ModularCurve_legendreJ_inv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_legendreJ_inv.lean)
-/
@[path]
private lemma main
  [Field K]
  {t : K} :
-- imply
  legendreJ t⁻¹ = legendreJ t :=
-- proof
  legendreJ_inv' t


-- created on 2026-10-23
