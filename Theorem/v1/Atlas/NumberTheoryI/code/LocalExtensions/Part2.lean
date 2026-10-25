/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Abbrev.v1.Atlas.NumberTheoryI.code.LocalExtensions


section MaxUnramifiedInvariance

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

theorem thm_9_22_integralClosure_isDVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra A E] [IsScalarTower A K E] [Algebra.IsSeparable K E] :
    IsDiscreteValuationRing ↥(integralClosure A E) := by

  haveI : IsLocalRing ↥(integralClosure A E) := integral_closure_isLocalRing A K E


  haveI : IsNoetherianRing ↥(integralClosure A E) :=
    integral_closure_isNoetherianRing A K E

  haveI : Ring.DimensionLEOne ↥(integralClosure A E) :=
    Ring.DimensionLEOne.isIntegralClosure A E (integralClosure A E)

  haveI : IsIntegrallyClosed ↥(integralClosure A E) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K

  haveI : IsDedekindDomain ↥(integralClosure A E) := {}

  haveI : IsPrincipalIdealRing ↥(integralClosure A E) := inferInstance

  have hNotField : IsLocalRing.maximalIdeal ↥(integralClosure A E) ≠ ⊥ := by
    rw [ne_eq, IsLocalRing.isField_iff_maximalIdeal_eq.symm]
    intro hField
    haveI : Algebra.IsIntegral A ↥(integralClosure A E) :=
      IsIntegralClosure.isIntegral_algebra A E
    have hInj : Function.Injective (algebraMap A ↥(integralClosure A E)) := by
      intro a b hab
      have h1 := congr_arg (algebraMap ↥(integralClosure A E) E) hab
      simp only [← IsScalarTower.algebraMap_apply] at h1
      have hinj : Function.Injective (algebraMap A E) := by
        rw [IsScalarTower.algebraMap_eq A K E]
        exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
      exact hinj h1
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hInj hField)

  exact IsDiscreteValuationRing.mk hNotField

theorem AKLB_intClE_isDVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.IsSeparable K L]
    (E : IntermediateField K L) :
    IsDiscreteValuationRing ↥(integralClosure A ↥E) := by
  haveI : FiniteDimensional K ↥E := IntermediateField.finiteDimensional_left E
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  exact thm_9_22_integralClosure_isDVR A K ↥E

end MaxUnramifiedInvariance
