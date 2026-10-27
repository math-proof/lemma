import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.of_const](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {X: Set ℝ}
  {c:ℝ}
-- given
  (h: ∀ x ∈ X, f x = c) :
-- imply
  ConstantOn f X :=
-- proof
  Chapter11.ConstantOn.of_const h


-- created on 2026-10-22
