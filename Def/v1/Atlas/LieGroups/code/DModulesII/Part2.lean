/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Support
public import Structure.v1.Atlas.LieGroups.code.DModuleApplications.Part5
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Abbrev.v1.Atlas.LieGroups.code.DModulesII

@[expose] public section

open CategoryTheory


namespace DModulesII

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

def annihilatedByIdeal (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] : Set M :=
  {v : M | ∀ f ∈ I, (ι f) • v = 0}

def annihilatedByIdealAddSubgroup (I : Ideal R) (M : Type*) [AddCommGroup M] [Module D M] :
    AddSubgroup M where
  carrier := annihilatedByIdeal ι I M
  zero_mem' := fun f _ => smul_zero _
  add_mem' := fun {a b} ha hb f hf => by
    show (ι f) • (a + b) = 0
    rw [smul_add, ha f hf, hb f hf, add_zero]
  neg_mem' := fun {a} ha f hf => by
    show (ι f) • (-a) = 0
    rw [smul_neg, ha f hf, neg_zero]

def DModSheafSupport (M : Type*) [AddCommGroup M] [Module D M] : Set (PrimeSpectrum R) :=
  @sheafSupport R _ M _ (rModuleOf ι M)

end DModules
end DModulesII
