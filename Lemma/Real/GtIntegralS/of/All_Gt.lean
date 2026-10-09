import Mathlib
import sympy.Basic
open Set MeasureTheory



@[path]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfc : ContinuousOn f (Icc a b))
  (hgc : ContinuousOn g (Icc a b))
  (hfg : ∀ x ∈ Ioo a b, f x > g x) :
-- imply
  (∫ x in a..b, f x) > ∫ x in a..b, g x := by
-- proof
  have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab.le
  have hgi : IntervalIntegrable g volume a b := hgc.intervalIntegrable_of_Icc hab.le
  have hpos : 0 < ∫ x in a..b, (f x - g x) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hfi.sub hgi) _ hab
    intro x hx
    apply sub_pos.mpr
    apply hfg x hx
  rw [intervalIntegral.integral_sub hfi hgi] at hpos
  linarith


-- created on 2026-10-07
