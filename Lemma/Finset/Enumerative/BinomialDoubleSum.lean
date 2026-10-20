import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BinomialDoubleSum
open MetaMathlibExt


/--
[binomial_double_sum_eq_pow_sub_fib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialDoubleSum.lean)
-/
@[path]
private lemma binomial_double_sum_eq_pow_sub_fib_eq
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n / 2 + 1),
    ∑ q ∈ Finset.range (n - 2 * k + 1), Nat.choose (n - k) q) =
    2 ^ (n + 1) - Nat.fib (n + 2) := by
-- proof
  apply MetaMathlibExt.binomial_double_sum_eq_pow_sub_fib n


-- created on 2026-10-20
