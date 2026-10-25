import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_iter_side_is_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B: Box d}
  {k : ℕ}
  {B' : Box d}
  {i : Fin d}
-- given
  (hB' : B' ∈ subdivide_iter B (k+1)) :
-- imply
  ∃ a b, B'.side i = Icc a b :=
-- proof
  Box.subdivide_iter_side_is_Icc B k B' hB' i


-- created on 2026-10-22
