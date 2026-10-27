import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.of_subsingleton](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {X: Set ℝ} [Subsingleton X]
  {f: ℝ → ℝ} :
-- imply
  ConstantOn f X :=
-- proof
  Chapter11.ConstantOn.of_subsingleton


-- created on 2026-10-22
