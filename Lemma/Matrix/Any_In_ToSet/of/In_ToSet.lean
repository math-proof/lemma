import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_iter_covers](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B : Box d}
  {k : ℕ}
  {x : EuclideanSpace' d}
-- given
  (hx : x ∈ B.toSet) :
-- imply
  ∃ B' ∈ subdivide_iter B k, x ∈ B'.toSet :=
-- proof
  Box.subdivide_iter_covers B k x hx


-- created on 2026-10-22
