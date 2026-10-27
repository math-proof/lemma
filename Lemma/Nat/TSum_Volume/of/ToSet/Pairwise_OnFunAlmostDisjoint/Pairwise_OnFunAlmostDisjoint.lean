import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.sum_volume_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {B B': ℕ → Box d}
-- given
  (hdisj: Pairwise (Function.onFun AlmostDisjoint B))
  (hdisj': Pairwise (Function.onFun AlmostDisjoint B'))
  (hcover: (⋃ n, (B n).toSet) = (⋃ n, (B' n).toSet)) :
-- imply
  ∑' n, (B n).volume = ∑' n, (B' n).volume :=
-- proof
  Box.sum_volume_eq B B' hdisj hdisj' hcover


-- created on 2026-10-22
