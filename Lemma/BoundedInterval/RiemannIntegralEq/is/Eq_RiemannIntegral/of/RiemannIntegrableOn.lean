import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval


/--
[riemann_integral_eq_iff_of_integrable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
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
