/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean -/

import Mathlib.Data.Nat.Prime.Defs

/-!
# Sophie Germain primes

This module defines the Sophie Germain prime predicate following arXiv:2311.13375,
lines 83–85: a prime `p` such that `2 * p + 1` is also prime. No oddness
restriction is imposed, so `p = 2` is included.

## Main definitions

* `Nat.IsSophieGermainPrime`

## Main statements

* `Nat.isSophieGermainPrime_iff`
* `Nat.IsSophieGermainPrime.prime`
* `Nat.IsSophieGermainPrime.prime_two_mul_add_one`
-/

namespace Nat

/-- A natural number `p` is a **Sophie Germain prime** if `p` is prime and
`2 * p + 1` is prime. This formalizes the definition in arXiv:2311.13375,
lines 83–85, which does not exclude `p = 2`. -/
def IsSophieGermainPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (2 * p + 1)
end Nat
