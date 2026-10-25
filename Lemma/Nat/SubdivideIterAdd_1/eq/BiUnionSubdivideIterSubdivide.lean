import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_iter_succ](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {k: ℕ} :
-- imply
  subdivide_iter B (k+1) = (subdivide_iter B k).biUnion Box.subdivide :=
-- proof
  Box.subdivide_iter_succ B k


-- created on 2026-10-22
