import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_3.Part7
open BoundedInterval
open TaggedPartition


/--
[TaggedPartition.uniform_norm](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {n: ℕ}
-- given
  (hn: n > 0)
  (hI: I = Icc I.a I.b)
  (hab: I.a < I.b) :
-- imply
  (TaggedPartition.uniform I n hn hI hab).norm = (I.b - I.a) / n :=
-- proof
  TaggedPartition.uniform_norm I n hn hI hab


-- created on 2026-10-22
