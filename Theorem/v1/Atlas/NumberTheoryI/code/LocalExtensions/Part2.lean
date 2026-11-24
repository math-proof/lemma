module
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Order.Hom.Lattice
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
public import Abbrev.v1.Atlas.NumberTheoryI.code.LocalExtensions


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
