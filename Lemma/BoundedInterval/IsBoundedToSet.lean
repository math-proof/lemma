import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval


/--
[BoundedInterval.isBounded](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  Bornology.IsBounded I.toSet :=
-- proof
  BoundedInterval.isBounded I


-- created on 2026-10-22
