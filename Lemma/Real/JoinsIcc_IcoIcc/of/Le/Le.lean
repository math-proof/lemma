import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Analysis.Section_11_1.Part8
open Chapter11.BoundedInterval
open Chapter11


/--
[BoundedInterval.join_Ico_Icc](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_1.lean)
-/
@[path]
private lemma main
  {a b c:ℝ}
-- given
  (hab: a ≤ b)
  (hbc: b ≤ c) :
-- imply
  (Icc a c).joins (Ico a b) (Icc b c) :=
-- proof
  Chapter11.BoundedInterval.join_Ico_Icc hab hbc


-- created on 2026-10-22
