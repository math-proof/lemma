-- Carved from Lemma/Definitions/Def_TaylorWiles_Primes.lean: instance decls only.
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lemma.TaylorWiles.Primes

set_option autoImplicit false


namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

instance isMaximal_ratPrimeIdeal (ℓ : ℕ) [Fact ℓ.Prime] : (ratPrimeIdeal ℓ).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp Fact.out).irreducible

variable {L}

variable (L)

end FrobeniusDensity

