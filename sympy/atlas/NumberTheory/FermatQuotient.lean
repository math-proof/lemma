/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatQuotient.lean -/

import Mathlib.FieldTheory.Finite.Basic

/-!
# Fermat quotient

This module defines the integer-valued Fermat quotient `q_p(a)` for a
prime modulus `p` and integer `a` coprime to `p`.
-/

namespace Int

/-- Fermat quotient `q_p(a) = (a ^ (p - 1) - 1) / p` for prime `p` and `a`
coprime to `p`. Integrality follows from `Int.prime_dvd_pow_sub_one`.
Proof arguments `_hp` and `_ha` are retained to enforce the domain
restriction to prime moduli and coprime integers, though the computed
value is independent of witnesses. -/
@[nolint unusedArguments]
def fermatQuotient (p : ℕ) (_hp : Nat.Prime p) (a : ℤ)
    (_ha : IsCoprime a (p : ℤ)) : ℤ :=
  (a ^ (p - 1) - 1) / (p : ℤ)

/-- Evaluation formula for the Fermat quotient. -/
theorem fermatQuotient_eq (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    fermatQuotient p hp a ha = (a ^ (p - 1) - 1) / (p : ℤ) :=
  rfl

/-- Exact recovery: `p * q_p(a) = a ^ (p - 1) - 1`. -/
theorem natCast_mul_fermatQuotient (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    (p : ℤ) * fermatQuotient p hp a ha = a ^ (p - 1) - 1 := by
  unfold fermatQuotient
  exact Int.mul_ediv_cancel' (Int.prime_dvd_pow_sub_one hp ha)

end Int
