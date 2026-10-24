/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/StirlingSecondExplicit.lean -/


import Lemma.Finset.Enumerative.StirlingSecondExplicit

open scoped BigOperators

namespace MetaMathlibExt

-- The explicit finite-difference formula is available through the shared API.
example (t k : ℕ) :
    (Nat.stirlingSecond t k : ℝ) * (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * Nat.choose k j * (j : ℝ) ^ t :=
  stirlingSecond_mul_factorial_eq_sum t k

-- The shifted Stirling-number exponential generating function is public.
example (j : ℕ) (x : ℝ) :
    HasSum
      (fun n : ℕ => (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial))
      (Real.exp x * (Real.exp x - 1) ^ j / j.factorial) :=
  hasSum_stirlingSecond_succ_egf j x

end MetaMathlibExt
