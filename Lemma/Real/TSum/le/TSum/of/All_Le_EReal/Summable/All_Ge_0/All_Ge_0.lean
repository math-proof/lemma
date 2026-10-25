import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[tsum_le_coe_tsum_of_forall_le](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f : ℕ → EReal}
  {g : ℕ → ℝ}
-- given
  (hf_nn : ∀ n, 0 ≤ f n)
  (hg_nn : ∀ n, 0 ≤ g n)
  (hg_sum : Summable g)
  (h_le : ∀ n, f n ≤ (g n : EReal)) :
-- imply
  ∑' n, f n ≤ (∑' n, g n : EReal) :=
-- proof
  EReal.tsum_le_coe_tsum_of_forall_le hf_nn hg_nn hg_sum h_le


-- created on 2026-10-20
