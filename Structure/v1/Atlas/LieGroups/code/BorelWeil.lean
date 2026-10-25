/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BorelWeil.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Rank
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.Algebra.Lie.Weights.RootSystem


noncomputable section

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
