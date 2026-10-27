import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box
open Box.IsDyadic


/--
[Box.IsDyadic.all_sides_Icc](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d}
-- given
  (hB : B.IsDyadic) :
-- imply
  ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b :=
-- proof
  Box.IsDyadic.all_sides_Icc hB


-- created on 2026-10-22
