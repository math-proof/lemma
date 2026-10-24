import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_7
open Chapter6.Sequence
open Real hiding rpow
open Chapter6
open Chapter6.Real


/--
[Real.ratPow_tendsto_rpow](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean)
-/
@[path]
private lemma main
  {x α:ℝ}
  {q: ℕ → ℚ}
-- given
  (hx: x > 0)
  (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
-- imply
  ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (Chapter6.Real.rpow x α) :=
-- proof
  Chapter6.Real.ratPow_tendsto_rpow hx hq


-- created on 2026-10-22
