import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.PrimitiveNondeficientBound
open MetaMathlibExt


/--
[primitive_nondeficient_prime_power_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/PrimitiveNondeficientBound.lean)
-/
@[path]
private lemma primitive_nondeficient_prime_power_bound_eq
  {n : ℕ}
-- given
  (hn : n ≠ 0)
  (hnondef : 2 * n ≤ ∑ d ∈ Nat.divisors n, d)
  (hprim : ∀ m ∈ Nat.divisors n, m < n → ∑ d ∈ Nat.divisors m, d < 2 * m) :
-- imply
  ∃ p ∈ n.primeFactors,
    p ^ (n.factorization p + 1) < 2 * n.primeFactors.card * ∏ q ∈ n.primeFactors, q := by
-- proof
  apply MetaMathlibExt.primitive_nondeficient_prime_power_bound n hn hnondef hprim


-- created on 2026-10-20
