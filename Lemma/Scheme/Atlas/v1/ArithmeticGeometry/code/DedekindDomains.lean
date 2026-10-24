import Mathlib
import sympy.Basic
open Ideal Ring


/--
[integrally_closed_noetherian_dim_one_localization_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DedekindDomains.lean)
-/
@[path]
lemma integrally_closed_noetherian_dim_one_localization_isDVR
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  [Ring.DimensionLEOne A]
  [IsIntegrallyClosed A]
  {P : Ideal A}
  [P.IsPrime]
-- given
  (hP : P ≠ ⊥) :
-- imply
  IsDiscreteValuationRing (Localization.AtPrime P) := by
-- proof
  haveI : IsDedekindDomain A :=
    (isDedekindDomain_iff A (FractionRing A)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        fun hx => (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hx⟩
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP
    (Localization.AtPrime P)


-- created on 2026-10-23
