module
public import Theorem.HahnSeries.JqCoeff
public import Theorem.LaurentSeries.LaurentCoeff
public import Instance.ModularCurve_PhiGen
public import Class.AlgebraicCurve_DivisorClassGroup
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Algebraic.Basic
public import Instance.AlgebraicCurve_PlacesOverDVR
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Def.ModularCurve_FibreModel
public import Instance.ModularCurve_ArithmeticGalois
public import Structure.ModularCurve_PlaceSpecialization
public import Theorem.IntermediateField.SpecializationMap
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_SpecializationMap.lean: instance decls only.

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
