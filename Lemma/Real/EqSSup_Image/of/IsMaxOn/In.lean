import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_9_6
open Chapter9
open Chapter9.sSup


/--
[sSup.of_isMaxOn](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {X:Set ℝ}
  {x₀:ℝ}
-- given
  (hx₀: x₀ ∈ X)
  (h: IsMaxOn f X x₀) :
-- imply
  sSup (f '' X) = f x₀ :=
-- proof
  Chapter9.sSup.of_isMaxOn hx₀ h


-- created on 2026-10-22
