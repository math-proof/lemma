/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

@[expose] public section

noncomputable section

open Ideal Polynomial

open scoped Pointwise

noncomputable def AdjoinRoot.quotientIso (A : Type*) [CommRing A] [IsLocalRing A]
    (g : Polynomial A) :
    (AdjoinRoot g ⧸ Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A)) ≃ₐ[A]
    (Polynomial (IsLocalRing.ResidueField A) ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))}) :=
  AdjoinRoot.quotEquivQuotMap g (IsLocalRing.maximalIdeal A)

end
