import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[bisect_fst_eq_endpoints](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I₁ I₂ : BoundedInterval}
-- given
  (h : I₁.bisect.fst = I₂.bisect.fst) :
-- imply
  I₁.a = I₂.a ∧ I₁.b = I₂.b :=
-- proof
  BoundedInterval.bisect_fst_eq_endpoints h


-- created on 2026-10-22
