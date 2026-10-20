import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.DixonCubicBinomial
open scoped BigOperators
open MetaMathlibExt


/--
[dixon_alternating_cubic_binomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DixonCubicBinomial.lean)
-/
@[path]
private lemma dixon_alternating_cubic_binomial_sum_eq
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range (2 * n + 1),
    (-1 : ℤ) ^ k * (Nat.choose (2 * n) k : ℤ) ^ 3 =
    (-1 : ℤ) ^ n * (Nat.choose (2 * n) n : ℤ) *
    (Nat.choose (3 * n) (2 * n) : ℤ) := by
-- proof
  apply MetaMathlibExt.dixon_alternating_cubic_binomial_sum n


-- created on 2026-10-20
