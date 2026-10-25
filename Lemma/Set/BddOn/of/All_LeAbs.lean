import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_6
open Chapter9
open Chapter9.BddOn


/--
[BddOn.of_bounded](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {f :ℝ → ℝ}
  {X: Set ℝ}
  {M:ℝ}
-- given
  (h: ∀ x ∈ X, |f x| ≤ M) :
-- imply
  BddOn f X :=
-- proof
  Chapter9.BddOn.of_bounded h


-- created on 2026-10-22
