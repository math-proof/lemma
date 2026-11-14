import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open TaggedPartition


/--
[TaggedPartition.nhds_zero_neBot](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
-- given
  (hI: I = Icc I.a I.b)
  (hab: I.a < I.b) :
-- imply
  Filter.NeBot (TaggedPartition.nhds_zero I) :=
-- proof
  TaggedPartition.nhds_zero_neBot I hI hab


-- created on 2026-10-22
