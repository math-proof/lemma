import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[tsum_le_of_sum_range_le_of_nonneg](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f : ℕ → EReal}
  {M : EReal}
-- given
  (h_nn : ∀ n, 0 ≤ f n)
  (h : ∀ N : ℕ, ∑ n ∈ Finset.range N, f n ≤ M) :
-- imply
  ∑' n, f n ≤ M :=
-- proof
  EReal.tsum_le_of_sum_range_le_of_nonneg h_nn h


-- created on 2026-10-20
