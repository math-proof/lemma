import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval


/--
[riemann_integral_eq_zero_of_zero_length](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f : ℝ → ℝ}
  {I : BoundedInterval}
  {R : ℝ}
-- given
  (h_eq : I.a = I.b)
  (h_len : |I|ₗ = 0)
  (hR : riemann_integral_eq f I R) :
-- imply
  R = 0 :=
-- proof
  riemann_integral_eq_zero_of_zero_length h_eq h_len hR


-- created on 2026-10-22
