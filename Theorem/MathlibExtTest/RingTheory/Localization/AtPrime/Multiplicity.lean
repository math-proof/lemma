/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/Localization/AtPrime/Multiplicity.lean -/


import Lemma.Int.Localization.AtPrime.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Different
set_option autoImplicit false

/-!
# Tests for ideal multiplicity under localization at a maximal ideal

Examples exercising `IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq`:
the generic canonical-localization application, the number-theory
specialization to `differentIdeal A B`, the correction-term specialization to
`Ideal.span {(e : B)}`, and a concrete integer localization at the prime `(5)`.
-/


/-- Generic ideal at the canonical localization `Localization.AtPrime p`. -/
example {R : Type*} [CommRing R] [IsDedekindDomain R]
    (p : Ideal R) [p.IsMaximal] (I : Ideal R) :
    emultiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (I.map (algebraMap R (Localization.AtPrime p))) =
      emultiplicity p I :=
  IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq p I

/-- Number-theory specialization: multiplicity of `differentIdeal A B`. -/
example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
    (P : Ideal B) [P.IsMaximal] :
    emultiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        ((differentIdeal A B).map (algebraMap B (Localization.AtPrime P))) =
      emultiplicity P (differentIdeal A B) :=
  IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq P _

/-- Correction-term specialization: `I = Ideal.span {(e : B)}`. -/
example {B : Type*} [CommRing B] [IsDedekindDomain B]
    (P : Ideal B) [P.IsMaximal] (e : B) :
    emultiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        ((Ideal.span {(e : B)}).map (algebraMap B (Localization.AtPrime P))) =
      emultiplicity P (Ideal.span {(e : B)}) :=
  IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq P _

