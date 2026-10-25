import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_6_7.Part2
open Chapter6.Sequence
open Real hiding rpow
open Chapter6
open Chapter6.Real


/--
[Real.rpow_eq_lim_ratPow](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean)
-/
@[path]
private lemma main
  {x α:ℝ}
  {q: ℕ → ℚ}
-- given
  (hx: x > 0)
  (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
-- imply
  Chapter6.Real.rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
-- proof
  Chapter6.Real.rpow_eq_lim_ratPow hx hq


-- created on 2026-10-22
