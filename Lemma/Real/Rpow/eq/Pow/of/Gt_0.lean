import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_6_7.Part2
open Chapter6.Sequence
open Real hiding rpow
open Chapter6
open Chapter6.Real


/--
[Real.rpow_of_rat_eq_ratPow](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean)
-/
@[path]
private lemma main
  {x:ℝ}
  {q: ℚ}
-- given
  (hx: x > 0) :
-- imply
  Chapter6.Real.rpow x (q:ℝ) = x^(q:ℝ) :=
-- proof
  Chapter6.Real.rpow_of_rat_eq_ratPow hx


-- created on 2026-10-22
