import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  Bornology.IsBounded I.toSet :=
-- proof
  BoundedInterval.isBounded I


-- created on 2026-10-22
