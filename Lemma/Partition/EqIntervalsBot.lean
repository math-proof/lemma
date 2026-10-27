import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Partition


/--
[Partition.intervals_of_bot](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I:BoundedInterval} :
-- imply
  (⊥:Partition I).intervals = {I} :=
-- proof
  Chapter11.Partition.intervals_of_bot I


-- created on 2026-10-22
