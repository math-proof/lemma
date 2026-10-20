import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.RamanujanTwoPrimes
open MathlibExt.NumberTheory.BreuschWanted


/--
[ramanujan_two_primes_between](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/RamanujanTwoPrimes.lean)
-/
@[path]
private lemma ramanujan_two_primes_between_eq
  {n : ℕ}
-- given
  (hn : 6 ≤ n) :
-- imply
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q < 2 * n := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.ramanujan_two_primes_between n hn


-- created on 2026-10-20
