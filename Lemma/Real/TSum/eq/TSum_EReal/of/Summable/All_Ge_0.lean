import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[coe_tsum_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {g : ℕ → ℝ}
-- given
  (hg_nn : ∀ n, 0 ≤ g n)
  (hg_sum : Summable g) :
-- imply
  (↑(∑' n, g n) : EReal) = ∑' n, (g n : EReal) :=
-- proof
  EReal.coe_tsum_of_nonneg hg_nn hg_sum


-- created on 2026-10-20
