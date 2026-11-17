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
public import Abbrev.v1.Atlas.LieGroups.code.DModulesII.Part2

@[expose] public section

open CategoryTheory


namespace DModulesII

section Equivariant

variable (k : Type*) [Field k]
         (G : Type*) [Group G]
         (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra k 𝔤]
         (D : Type*) [Ring D] [Algebra k D]

def monodromic_rho_phi
    {M : Type*} [AddCommGroup M] [Module k M] [Module D M]
    (W : WeaklyEquivDModule k G D M)
    (lieAction_phi : 𝔤 →ₗ[k] Module.End k M)
    (lieToD : 𝔤 →ₗ⁅k⁆ D) (x : 𝔤) (v : M) : M :=
  rho_phi k G 𝔤 D W lieAction_phi lieToD x v

end Equivariant
end DModulesII
