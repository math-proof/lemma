import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
@[path]
private lemma main
  {I: BoundedInterval} :
-- imply
  0 ≤ I.length :=
-- proof
  BoundedInterval.length_nonneg I


-- created on 2026-10-22
