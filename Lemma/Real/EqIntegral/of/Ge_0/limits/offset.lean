import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b c : ℝ} :
-- imply
  ∫ x in a..b, f (x + c) = ∫ x in a + c..b + c, f x :=
-- proof
  intervalIntegral.integral_comp_add_right f c


-- created on 2026-10-11
-- updated on 2026-10-26
