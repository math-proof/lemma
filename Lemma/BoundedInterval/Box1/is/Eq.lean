import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[BoundedInterval.toBox_inj](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  (I:Box 1) = (J:Box 1) ↔ I = J :=
-- proof
  BoundedInterval.toBox_inj


-- created on 2026-10-22
