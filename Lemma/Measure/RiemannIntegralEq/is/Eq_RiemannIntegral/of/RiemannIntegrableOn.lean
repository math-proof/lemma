import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
  {R:ℝ}
-- given
  (h: RiemannIntegrableOn f I) :
-- imply
  riemann_integral_eq f I R ↔ R = riemannIntegral f I :=
-- proof
  riemann_integral_eq_iff_of_integrable h R


-- created on 2026-10-22
