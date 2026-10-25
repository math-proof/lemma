/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Localization/AtPrime/Multiplicity.lean -/


import Lemma.Int.Localization.AtPrime.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Different
import Theorem.MathlibExtTest.RingTheory.Localization.AtPrime.Multiplicity
set_option autoImplicit false

/-!
# Tests for ideal multiplicity under localization at a maximal ideal

Examples exercising `IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq`:
the generic canonical-localization application, the number-theory
specialization to `differentIdeal A B`, the correction-term specialization to
`Ideal.span {(e : B)}`, and a concrete integer localization at the prime `(5)`.
-/


/-- Closed primality facts for the integer prime ideal `(5)`. -/
instance : (Ideal.span {(5 : ℤ)}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime
    (Int.prime_iff_natAbs_prime.mpr (by decide))

/-- Closed maximality fact for the integer prime ideal `(5)`. -/
instance : (Ideal.span {(5 : ℤ)}).IsMaximal :=
  (Int.prime_iff_natAbs_prime.mpr (by decide)).isMaximal_span_singleton

