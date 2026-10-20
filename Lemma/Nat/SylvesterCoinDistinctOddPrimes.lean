import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterCoinDistinctOddPrimes
open MetaMathlibExt


/--
[sylvester_coin_distinct_odd_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterCoinDistinctOddPrimes.lean)
-/
@[path]
private lemma sylvester_coin_distinct_odd_primes_eq
  {p q : ℕ}
-- given
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (hodd : Odd p ∧ Odd q)
  (hne : p ≠ q) :
-- imply
  Nat.card { n : ℕ // ¬ ∃ x y : ℕ, n = p * x + q * y }
    = (p - 1) * (q - 1) / 2 := by
-- proof
  apply MetaMathlibExt.sylvester_coin_distinct_odd_primes p q hp hq hodd hne


-- created on 2026-10-20
