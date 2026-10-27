import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_10_1.Part2


/--
[of_hasDeriv](https://github.com/teorth/analysis/blob/main/Analysis/Section_10_1.lean)
-/
@[path]
private lemma main
  {X: Set ℝ}
  {x₀ : ℝ}
  {f: ℝ → ℝ}
  {L:ℝ}
-- given
  (hL: HasDerivWithinAt f L X x₀) :
-- imply
  DifferentiableWithinAt ℝ f X x₀ :=
-- proof
  DifferentiableWithinAt.of_hasDeriv hL


-- created on 2026-10-20
