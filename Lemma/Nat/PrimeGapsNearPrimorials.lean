import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeGapsNearPrimorials
open MetaMathlibExt


/--
[prime_sub_primorial_prime_of_between_consecutive_primes_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
private lemma prime_sub_primorial_prime_of_between_consecutive_primes_general_eq
  {q r p : ℕ}
-- given
  (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) := by
-- proof
  apply MetaMathlibExt.prime_sub_primorial_prime_of_between_consecutive_primes_general hconsecutive hp hlower hupper

/--
[prime_sub_primorial_prime_of_between_consecutive_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
private lemma prime_sub_primorial_prime_of_between_consecutive_primes_eq
  {q r p : ℕ}
-- given
  (hq : Nat.Prime q)
  (hr : Nat.Prime r)
  (hqr : q < r)
  (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) := by
-- proof
  apply MetaMathlibExt.prime_sub_primorial_prime_of_between_consecutive_primes hq hr hqr hconsecutive hp hlower hupper

/--
[AreConsecutivePrimes.prime_sub_primorial_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
private lemma AreConsecutivePrimes_prime_sub_primorial_prime_eq
  {q r p : ℕ}
-- given
  (hqr : AreConsecutivePrimes q r)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) := by
-- proof
  apply MetaMathlibExt.AreConsecutivePrimes.prime_sub_primorial_prime hqr hp hlower hupper


-- created on 2026-10-20
