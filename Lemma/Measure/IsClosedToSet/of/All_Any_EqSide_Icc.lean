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
  (h : ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b) :
-- imply
  IsClosed B.toSet :=
-- proof
  Box.isClosed_toSet_of_Icc B h


-- created on 2026-10-22
