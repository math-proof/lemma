/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/Period.lean -/

import Mathlib.Algebra.Ring.Periodic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Periods of multiplicative maps `ℤ →* R` and Dirichlet moduli

This module is a carrier repair of ATLAS `NumberTheoryI` Lemma 18.8: a normalized
totally multiplicative function `χ` on the integers with least positive additive
period `m` is a Dirichlet character of modulus `m'` if and only if `m ∣ m'` and
`m' ∣ m ^ k` for some `k`.

ATLAS carries `χ` as an `ArithmeticFunction ℂ`, which forces `χ 0 = 0`; period `1`
then gives `χ 1 = 0`, contradicting normalization.  Here `χ : ℤ →* R` bakes in
`χ 1 = 1` and multiplicativity without constraining `χ 0`, so the principal
modulus-`1` character is nonvacuous.

## Main definitions

* `MonoidHom.IsDirichletCharacterModulus`: `χ` is `q`-periodic and vanishes exactly
  off the integers coprime to `q`.

## Main statements

* `MonoidHom.isDirichletCharacterModulus_iff`: the modulus characterization above.
* `MonoidHom.isDirichletCharacterModulus_self`: `χ` has modulus `m` itself.
-/

namespace MonoidHom

variable {R : Type*} [MonoidWithZero R]

/-- `χ` is a Dirichlet character of modulus `q`: it is `q`-periodic and its
nonvanishing locus is exactly the set of integers coprime to `q`. -/
def IsDirichletCharacterModulus (χ : ℤ →* R) (q : ℕ) : Prop :=
  Function.Periodic χ (q : ℤ) ∧ ∀ n : ℤ, χ n ≠ 0 ↔ IsCoprime (q : ℤ) n
end MonoidHom
