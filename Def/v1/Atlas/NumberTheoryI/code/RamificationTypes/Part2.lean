/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RamificationTypes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.NumberTheoryI.code.EisensteinRamified
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EisensteinRamified
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Thm1023
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor1015
import Theorem.v1.Atlas.NumberTheoryI.code.Thm1023
import Abbrev.v1.Atlas.NumberTheoryI.code.Cor1015
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Structure.v1.Atlas.NumberTheoryI.code.RamificationTypes
open Ideal IsLocalRing


section RamificationTransitivity

variable {p e_EK e_EL e_LK : ℕ}

noncomputable def intClE_to_L_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] L :=
  (E.val.restrictScalars A).comp (integralClosure A ↥E).val

noncomputable def intClE_to_B_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] B := by
  letI : Algebra ↥(integralClosure A ↥E) L :=
    (intClE_to_L_algHom A E).toAlgebra
  haveI : IsScalarTower A ↥(integralClosure A ↥E) L :=
    IsScalarTower.of_algHom (intClE_to_L_algHom A E)
  haveI : Algebra.IsIntegral A ↥(integralClosure A ↥E) :=
    integralClosure.AlgebraIsIntegral
  exact IsIntegralClosure.lift A B L

noncomputable def ramIdx_sub
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L) : ℕ := by
  haveI : IsDiscreteValuationRing ↥(integralClosure A ↥E) :=
    AKLB_intClE_isDVR A K L E
  exact (IsLocalRing.maximalIdeal A).ramificationIdx
    (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E))

noncomputable def ramIdx_over
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L) : ℕ := by
  haveI : IsDiscreteValuationRing ↥(integralClosure A ↥E) :=
    AKLB_intClE_isDVR A K L E
  letI : Algebra ↥(integralClosure A ↥E) B :=
    (intClE_to_B_algHom A B E).toAlgebra
  exact (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E)).ramificationIdx
    (IsLocalRing.maximalIdeal B)

end RamificationTransitivity
