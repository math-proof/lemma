import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_10_1.Part2


/--
[of_differentiableOn](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {f: ℝ → ℝ}
-- given
  (h: DifferentiableOn ℝ f X) :
-- imply
  ContinuousOn f X :=
-- proof
  ContinuousOn.of_differentiableOn h


-- created on 2026-10-20
