import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open RiemannIntegrable


/--
[RiemannIntegrable.of_zero_length](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {I: BoundedInterval}
  {a : ℝ}
-- given
  (h: I = Icc a a) :
-- imply
  RiemannIntegrableOn f I ∧ riemannIntegral f I = 0 :=
-- proof
  RiemannIntegrable.of_zero_length f h


-- created on 2026-10-22
