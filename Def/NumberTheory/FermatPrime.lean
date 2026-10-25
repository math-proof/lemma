/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatPrime.lean -/

import Mathlib.NumberTheory.Fermat
/-!
# Fermat primes

This module formalizes the notion of a Fermat prime.
-/


namespace MetaMathlibExt

/-- A Fermat prime: a prime of the form `2 ^ (2 ^ k) + 1`.

Cites stable source identifiers: concept `jis_sem_dc0cba6ecb4751a4e9031492`
("Fermat prime"), statements `jis_0d9f8f95b9a74c9ccfec1e18` and
`jis_a9e59051940d13024a23765b`. Formulated via `Nat.fermatNumber`. -/
def IsFermatPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ k : ℕ, p = Nat.fermatNumber k

end MetaMathlibExt
