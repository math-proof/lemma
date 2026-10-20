import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.AlternatingBinomialPartialSum
open MetaMathlibExt


/--
[alternating_binomial_partial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AlternatingBinomialPartialSum.lean)
-/
@[path]
private lemma alternating_binomial_partial_sum_eq
  {a : ℕ → ℂ}
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (-1 : ℂ) ^ k * (Nat.choose n k : ℂ) * (∑ j ∈ Finset.Icc 1 k, a j)) =
    ∑ k ∈ Finset.range n,
    (-1 : ℂ) ^ (k + 1) * (Nat.choose (n - 1) k : ℂ) * a (k + 1) := by
-- proof
  apply MetaMathlibExt.alternating_binomial_partial_sum a n


-- created on 2026-10-20
