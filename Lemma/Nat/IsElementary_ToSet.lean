import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Box


/--
[Box.sdiff](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B C: Box d} :
-- imply
  IsElementary (B.toSet \ C.toSet) :=
-- proof
  Box.sdiff B C


-- created on 2026-10-22
