import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[tsum_add_le_of_nonneg_pointwise](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f g h : ℕ → ℝ}
-- given
  (hf_nn : ∀ n, 0 ≤ f n)
  (hg_nn : ∀ n, 0 ≤ g n)
  (h_pw : ∀ n, f n + g n ≤ h n) :
-- imply
  (∑' n, (f n).toEReal) + (∑' n, (g n).toEReal) ≤ ∑' n, (h n).toEReal :=
-- proof
  EReal.tsum_add_le_of_nonneg_pointwise hf_nn hg_nn h_pw


-- created on 2026-10-20
