import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[bisect_length_sum](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I : BoundedInterval} :
-- imply
  |(I.bisect.fst)|ₗ + |(I.bisect.snd)|ₗ = |I|ₗ :=
-- proof
  BoundedInterval.bisect_length_sum I


-- created on 2026-10-22
