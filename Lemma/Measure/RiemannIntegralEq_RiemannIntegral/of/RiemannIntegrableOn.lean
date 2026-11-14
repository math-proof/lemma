import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
@[path]
private lemma main
  {f:ℝ → ℝ}
  {I: BoundedInterval}
-- given
  (h: RiemannIntegrableOn f I) :
-- imply
  riemann_integral_eq f I (riemannIntegral f I) :=
-- proof
  riemann_integral_of_integrable h


-- created on 2026-10-22
