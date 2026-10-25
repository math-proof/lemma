/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/DifferentLocalization.lean -/


import Instance.RingTheory.DedekindDomain.DifferentLocalization
import Lemma.Int.DedekindDomain.DifferentLocalization
set_option autoImplicit false

universe u

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)

/-!
# Tests for different ideals under canonical localization (ATLAS N241)

Generic application examples exercising
`FractionalIdeal.extendedHom_dual_one_eq_dual_one_ofField` and
`Ideal.map_differentIdeal_eq_localization_ofField`, plus a membership-facing
consequence of the fractional equality. These are API/inference tests; no new
definitions are introduced.
-/


local notation "Aₛ" => Localization.subalgebra.ofField K S hS

