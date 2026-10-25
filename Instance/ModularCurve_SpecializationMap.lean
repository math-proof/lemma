-- Carved from Lemma/Definitions/Def_ModularCurve_SpecializationMap.lean: instance decls only.
import Lemma.ModularCurve.JqCoeff
import Lemma.ModularCurve.LaurentCoeff
import Instance.ModularCurve_PhiGen
import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Algebraic.Basic
import Instance.AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Def.ModularCurve_FibreModel
import Instance.ModularCurve_ArithmeticGalois
import Structure.ModularCurve_PlaceSpecialization
import Lemma.ModularCurve.SpecializationMap

set_option autoImplicit false

noncomputable section


set_option autoImplicit false

noncomputable section


noncomputable section


set_option autoImplicit false

open Polynomial


set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

variable (A : ValuationSubring K)

private instance centre_isPrime : (w.centre A).IsPrime := Ideal.comap_isPrime _ _

private instance centre_isMaximal : (w.centre A).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (w.value_surjective A)

end Place

end AlgebraicCurve

set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open IsLocalRing IsDedekindDomain


namespace ValuationSubring

variable {F : Type*} [Field F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (O : ValuationSubring F)

private instance centreOver_isPrime (hO : ∀ r : R, algebraMap R F r ∈ O) : (O.centreOver hO).IsPrime
    :=
  Ideal.comap_isPrime _ _

end ValuationSubring


set_option autoImplicit false

open IsLocalRing Polynomial


set_option autoImplicit false

noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField Polynomial


set_option autoImplicit false

open Polynomial


set_option autoImplicit false


end
end
end
end
end
end
