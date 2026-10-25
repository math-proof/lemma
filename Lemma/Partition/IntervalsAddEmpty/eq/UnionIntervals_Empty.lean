import Mathlib
import sympy.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Partition


/--
[Partition.intervals_of_add_empty](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I: BoundedInterval}
  {P: Partition I} :
-- imply
  (P.add_empty).intervals = P.intervals ∪ {∅} :=
-- proof
  Chapter11.Partition.intervals_of_add_empty I P


-- created on 2026-10-22
