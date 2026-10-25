import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_9_6
open Chapter9
open Chapter9.sInf


/--
[sInf.of_isMinOn](https://github.com/teorth/analysis/blob/main/Analysis/Section_9_6.lean)
-/
@[path]
private lemma main
  {f:ℝ → ℝ}
  {X:Set ℝ}
  {x₀:ℝ}
-- given
  (hx₀: x₀ ∈ X)
  (h: IsMinOn f X x₀) :
-- imply
  sInf (f '' X) = f x₀ :=
-- proof
  Chapter9.sInf.of_isMinOn hx₀ h


-- created on 2026-10-22
