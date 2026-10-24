import Mathlib
import sympy.Basic
import sympy.analysis.Section_11_1
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.Partition


/--
[Partition.intervals_of_join](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I J K:BoundedInterval}
  {h:K.joins I J}
  {P: Partition I}
  {Q: Partition J} :
-- imply
  (P.join Q h).intervals = P.intervals ∪ Q.intervals :=
-- proof
  Chapter11.Partition.intervals_of_join P Q


-- created on 2026-10-22
