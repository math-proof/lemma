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

@[expose] public section

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
