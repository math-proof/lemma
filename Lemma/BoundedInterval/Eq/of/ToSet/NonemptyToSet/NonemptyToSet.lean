import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[toSet_injective_of_nonempty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {I J : BoundedInterval}
-- given
  (hI : I.toSet.Nonempty)
  (hJ : J.toSet.Nonempty)
  (h_eq : I.toSet = J.toSet) :
-- imply
  I = J :=
-- proof
  BoundedInterval.toSet_injective_of_nonempty hI hJ h_eq


-- created on 2026-10-22
