import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_11_2.Part6
open Chapter11.BoundedInterval
open Chapter11


/--
[constant_value_on_congr](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_2.lean)
-/
@[path]
private lemma main
  {f g: ℝ → ℝ}
  {X: Set ℝ}
-- given
  (h: ∀ x ∈ X, f x = g x) :
-- imply
  constant_value_on f X = constant_value_on g X :=
-- proof
  Chapter11.constant_value_on_congr h


-- created on 2026-10-22
