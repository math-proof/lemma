/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Support
import Structure.v1.Atlas.LieGroups.code.DModuleApplications.Part5
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Abbrev.v1.Atlas.LieGroups.code.DModulesII
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
