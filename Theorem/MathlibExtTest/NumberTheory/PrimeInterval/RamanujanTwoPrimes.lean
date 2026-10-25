/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeInterval/RamanujanTwoPrimes.lean -/


import Lemma.Nat.PrimeInterval.RamanujanTwoPrimes


namespace MathlibExtTest.NumberTheory.PrimeInterval.RamanujanTwoPrimes

example : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 6 < p ∧ p < q ∧ q < 2 * 6 :=
  MathlibExt.NumberTheory.BreuschWanted.ramanujan_two_primes_between 6 (by decide)

end MathlibExtTest.NumberTheory.PrimeInterval.RamanujanTwoPrimes
