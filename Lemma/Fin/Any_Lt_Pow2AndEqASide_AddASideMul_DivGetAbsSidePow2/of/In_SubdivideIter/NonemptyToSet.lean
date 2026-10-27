import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[subdivide_iter_side_grid](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B : Box d}
  {k : ℕ}
  {B' : Box d}
  {i : Fin d}
-- given
  (hB : B.toSet.Nonempty)
  (hB' : B' ∈ subdivide_iter B k) :
-- imply
  ∃ j : ℕ, j < 2^k ∧ (B'.side i).a = (B.side i).a + j * (|B.side i|ₗ / 2^k) :=
-- proof
  Box.subdivide_iter_side_grid B hB k B' hB' i


-- created on 2026-10-22
