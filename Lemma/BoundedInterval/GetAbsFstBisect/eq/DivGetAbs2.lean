import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval


/--
[bisect_fst_length](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval} :
-- imply
  |(I.bisect.fst)|ₗ = |I|ₗ / 2 :=
-- proof
  BoundedInterval.bisect_fst_length I


-- created on 2026-10-22
