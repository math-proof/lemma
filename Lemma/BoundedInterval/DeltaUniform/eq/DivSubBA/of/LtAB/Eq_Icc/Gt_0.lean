import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_3
open BoundedInterval
open TaggedPartition


/--
[TaggedPartition.uniform_delta](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_3.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {n: ℕ}
  {i: Fin n}
-- given
  (hn: n > 0)
  (hI: I = Icc I.a I.b)
  (hab: I.a < I.b) :
-- imply
  (TaggedPartition.uniform I n hn hI hab).delta i = (I.b - I.a) / n :=
-- proof
  TaggedPartition.uniform_delta hn hI hab i


-- created on 2026-10-22
