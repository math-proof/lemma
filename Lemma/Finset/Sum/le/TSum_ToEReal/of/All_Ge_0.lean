import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[finset_sum_le_tsum](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f : ℕ → ℝ}
  {t : Finset ℕ}
-- given
  (hf : ∀ n, 0 ≤ f n) :
-- imply
  (∑ n ∈ t, f n : EReal) ≤ ∑' n, (f n).toEReal :=
-- proof
  EReal.finset_sum_le_tsum hf t


-- created on 2026-10-20
