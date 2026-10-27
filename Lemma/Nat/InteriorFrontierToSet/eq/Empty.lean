import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.interior_frontier_eq_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d} :
-- imply
  interior (frontier B.toSet) = ∅ :=
-- proof
  Box.interior_frontier_eq_empty B


-- created on 2026-10-22
