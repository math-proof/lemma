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
import Abbrev.v1.Atlas.LieGroups.code.DModulesII.Part2
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
