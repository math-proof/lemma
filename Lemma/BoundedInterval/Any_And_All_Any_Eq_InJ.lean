import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise


/--
[BoundedInterval.partition](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {S: Finset BoundedInterval} :
-- imply
  ∃ T: Finset BoundedInterval, (T : Set _).PairwiseDisjoint BoundedInterval.toSet ∧ ∀ I ∈ S, ∃ U : Set T, I = ⋃ J ∈ U, J.val.toSet :=
-- proof
  BoundedInterval.partition S


-- created on 2026-10-22
