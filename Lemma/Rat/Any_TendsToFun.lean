import Mathlib
import sympy.Basic
import sympy.analysis.Section_6_7
open Chapter6.Sequence Real
open Chapter6
open Chapter6.Real


/--
[Real.eq_lim_of_rat](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_7.lean)
-/
@[path]
private lemma main
  {α:ℝ} :
-- imply
  ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α :=
-- proof
  Chapter6.Real.eq_lim_of_rat α


-- created on 2026-10-22
