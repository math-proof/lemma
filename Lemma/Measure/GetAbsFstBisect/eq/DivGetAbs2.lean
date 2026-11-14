import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
@[path]
private lemma main
  {I : BoundedInterval} :
-- imply
  |(I.bisect.fst)|ₗ = |I|ₗ / 2 :=
-- proof
  BoundedInterval.bisect_fst_length I


-- created on 2026-10-22
