import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
@[path]
private lemma main
  {I:BoundedInterval} :
-- imply
  (I:Box 1).toSet = Real.equiv_EuclideanSpace' '' I.toSet :=
-- proof
  BoundedInterval.coe_of_box I


-- created on 2026-10-22
