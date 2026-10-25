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
open CategoryTheory


namespace DModulesII

def IsSupportedOn {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) : Prop :=
  ∀ (f : R), f ∈ I → ∀ (v : M), ∃ N : ℕ, (f ^ N) • v = 0

def sheafSupport (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Set (PrimeSpectrum R) :=
  ⋂ (I : Ideal R) (_ : IsSupportedOn M I), PrimeSpectrum.zeroLocus (I : Set R)

section DModules

variable {R : Type*} [CommRing R] {D : Type*} [Ring D] (ι : R →+* D)

@[reducible]
def rModuleOf (M : Type*) [AddCommGroup M] [Module D M] : Module R M :=
  Module.compHom M ι

def DModIsSupportedOn (M : Type*) [AddCommGroup M] [Module D M] (I : Ideal R) : Prop :=
  @IsSupportedOn R _ M _ (rModuleOf ι M) I

end DModules
end DModulesII
