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
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions


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

noncomputable def integral_closure_residueField_fintype
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Fintype (IsLocalRing.ResidueField A)]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] [Algebra.IsSeparable K L]
    [IsLocalRing ↥(integralClosure A L)] :
    Fintype (IsLocalRing.ResidueField ↥(integralClosure A L)) := by
  set B := ↥(integralClosure A L) with hB_def

  haveI : Module.Finite A B := integral_closure_module_finite A K L


  haveI : FaithfulSMul A B := by
    have hinj : Function.Injective (algebraMap A B) := by
      intro a b hab
      have hinj_AL : Function.Injective (algebraMap A L) := by
        intro x y hxy
        apply IsFractionRing.injective A K; apply (algebraMap K L).injective
        rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      apply hinj_AL
      have key : ∀ x, algebraMap A L x = ↑(algebraMap A B x) := fun _ => rfl
      rw [key, key, hab]
    exact ⟨fun h => hinj (by
      have := h 1; rwa [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this)⟩
  haveI : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B

  haveI : Finite (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.finite_of_finite (R := A) (S := B) (Finite.of_fintype _)
  exact Fintype.ofFinite _

end MaxUnramifiedInvariance
