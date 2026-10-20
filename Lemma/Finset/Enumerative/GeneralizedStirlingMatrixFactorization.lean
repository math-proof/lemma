import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GeneralizedStirlingMatrixFactorization
open MetaMathlibExt


/--
[generalized_stirling_matrix_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingMatrixFactorization.lean)
-/
@[path]
private lemma generalized_stirling_matrix_factorization_eq
  {S : ℝ → ℝ → ℝ → ℕ → ℕ → ℝ}
  {α β γ : ℝ}
  {n k : ℕ}
-- given
  (hS : ∀ (a b c : ℝ) (n : ℕ) (x : ℝ), (∏ i ∈ Finset.range n, (x - (i : ℝ) * a)) = ∑ k ∈ Finset.range (n + 1), S a b c n k * ∏ i ∈ Finset.range k, ((x - c) - (i : ℝ) * b))
  (hzero : ∀ (a b c : ℝ) (n k : ℕ), n < k → S a b c n k = 0) :
-- imply
  S α β γ n k =
    ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (j + 1),
    S α 0 0 n j * S 0 0 γ j l * S 0 β 0 l k := by
-- proof
  apply MetaMathlibExt.generalized_stirling_matrix_factorization S hS hzero α β γ n k


-- created on 2026-10-20
