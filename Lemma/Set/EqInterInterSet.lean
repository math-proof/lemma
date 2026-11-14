import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.inter_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {I J: BoundedInterval} :
-- imply
  (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ) :=
-- proof
  Chapter11.BoundedInterval.inter_eq I J


-- created on 2026-10-22
