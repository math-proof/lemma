import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.ChebyshevUCoefficients

open scoped BigOperators
open MetaMathlibExt

/--
[chebyshevU_coeff_eq_binomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/ChebyshevUCoefficients.lean)
-/
@[path]
private lemma chebyshevU_coeff_eq_binomial_sum_eq
-- given
  (n k : ℕ) (hk : k ≤ n) :
-- imply
  (Polynomial.Chebyshev.U ℤ (n : ℤ)).coeff k =
    if n % 2 = k % 2 then
      (-1 : ℤ) ^ ((n - k) / 2) *
        ∑ i ∈ Finset.range (k + 1),
          ((Nat.choose ((n + k) / 2) i : ℕ) : ℤ) *
            ((Nat.choose ((n + k) / 2 - i) ((n - k) / 2) : ℕ) : ℤ)
    else 0 := by
-- proof
  apply chebyshevU_coeff_eq_binomial_sum
  exact hk


-- created on 2026-10-09
