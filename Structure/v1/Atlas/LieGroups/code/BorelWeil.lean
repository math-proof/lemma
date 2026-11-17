/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Rank
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.Algebra.Lie.Weights.RootSystem


public noncomputable section

universe u v

structure BorelWeilData where
  (k : Type u)
  [field_k : Field k]
  (𝔤 : Type v)
  [lieRing : LieRing 𝔤]
  [lieAlgebra : LieAlgebra k 𝔤]
  (G : Type*)
  [group_G : Group G]
  (WeightLattice : Type*)
  [wl_addCommGroup : AddCommGroup WeightLattice]
  (IsDominant : WeightLattice → Prop)
  (IrrepModule : WeightLattice → Type*)
  [irrepAddCommGroup : ∀ w, AddCommGroup (IrrepModule w)]
  [irrepModule : ∀ w, Module k (IrrepModule w)]
  [irrepFinDim : ∀ w, Module.Finite k (IrrepModule w)]
  (irrepRep : ∀ w, Representation k G (IrrepModule w))

  (FlagVar : Type*)
  (GlobalSections : WeightLattice → Type*)
  [sectionsAddCommGroup : ∀ w, AddCommGroup (GlobalSections w)]
  [sectionsModule : ∀ w, Module k (GlobalSections w)]
  (sectionsRep : ∀ w, Representation k G (GlobalSections w))

attribute [instance] BorelWeilData.field_k BorelWeilData.lieRing BorelWeilData.lieAlgebra
  BorelWeilData.group_G BorelWeilData.wl_addCommGroup BorelWeilData.irrepAddCommGroup
  BorelWeilData.irrepModule BorelWeilData.irrepFinDim BorelWeilData.sectionsAddCommGroup
  BorelWeilData.sectionsModule

structure ParabolicBorelWeilData extends BorelWeilData where
  (SimpleRoots : Type*)
  (S : Set SimpleRoots)
  (coroot_pairing : WeightLattice → SimpleRoots → ℤ)
  (PartialFlagVar : Type*)
  (projection : FlagVar → PartialFlagVar)
  (PartialFlagSections : WeightLattice → Type*)
  [pfSectionsAddCommGroup : ∀ w, AddCommGroup (PartialFlagSections w)]
  [pfSectionsModule : ∀ w, Module k (PartialFlagSections w)]
  (pfSectionsRep : ∀ w, Representation k G (PartialFlagSections w))

end
