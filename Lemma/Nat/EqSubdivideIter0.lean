import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_1
open BoundedInterval
open Box


/--
[subdivide_iter_zero](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d} :
-- imply
  subdivide_iter B 0 = {B} :=
-- proof
  Box.subdivide_iter_zero B


-- created on 2026-10-22
