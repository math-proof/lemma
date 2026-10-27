import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11
open Chapter11.ConstantOn


/--
[ConstantOn.eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f: ℝ → ℝ}
  {X: Set ℝ}
  {x:ℝ}
-- given
  (h: ConstantOn f X)
  (hx: x ∈ X) :
-- imply
  f x = constant_value_on f X :=
-- proof
  Chapter11.ConstantOn.eq h hx


-- created on 2026-10-22
