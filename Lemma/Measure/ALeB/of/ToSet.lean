import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
@[path]
private lemma main
  {I : BoundedInterval}
-- given
  (h : I.toSet.Nonempty) :
-- imply
  I.a ≤ I.b :=
-- proof
  BoundedInterval.nonempty_implies_le I h


-- created on 2026-10-22
