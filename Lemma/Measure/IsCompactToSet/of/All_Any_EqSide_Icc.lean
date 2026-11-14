import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box
@[path]
private lemma main
  {d : ℕ}
  {B : Box d}
-- given
  (h_closed : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) :
-- imply
  IsCompact B.toSet :=
-- proof
  Box.isCompact B h_closed


-- created on 2026-10-22
