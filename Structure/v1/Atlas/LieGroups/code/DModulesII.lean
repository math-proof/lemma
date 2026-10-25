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
import Class.v1.Atlas.LieGroups.code.DModulesII
open CategoryTheory


namespace DModulesII

section GEquivariantSheafDef

universe u_sheaf

structure QCohSheafData (k : Type u_sheaf) [Field k] where
  affineIndex : Type u_sheaf
  coordRing : affineIndex → Type u_sheaf
  [instCommRing : ∀ i, CommRing (coordRing i)]
  [instAlgebra : ∀ i, Algebra k (coordRing i)]
  diffOpsRing : affineIndex → Type u_sheaf
  [instDiffRing : ∀ i, Ring (diffOpsRing i)]
  sections : affineIndex → Type u_sheaf
  [instAddCommGroup : ∀ i, AddCommGroup (sections i)]
  [instModule : ∀ i, Module (diffOpsRing i) (sections i)]
  [instModuleK : ∀ i, Module k (sections i)]

attribute [instance] QCohSheafData.instCommRing QCohSheafData.instAlgebra
  QCohSheafData.instDiffRing QCohSheafData.instAddCommGroup QCohSheafData.instModule
  QCohSheafData.instModuleK

structure GEquivariantSheaf (k : Type u_sheaf) [Field k]
    (G : Type u_sheaf) [Group G] where
  sheafData : QCohSheafData k
  [mulAction : MulAction G sheafData.affineIndex]
  phi : (g : G) → (i : sheafData.affineIndex) →
    sheafData.sections i ≃ₗ[k] sheafData.sections (g • i)
  cocycle : ∀ (g h : G) (i : sheafData.affineIndex) (v : sheafData.sections i),
    (mul_smul g h i) ▸ (phi (g * h) i v) =
    phi g (h • i) (phi h i v)
  phi_one : ∀ (i : sheafData.affineIndex) (v : sheafData.sections i),
    (one_smul G i) ▸ (phi 1 i v) = v

end GEquivariantSheafDef


section Equivariant

variable (k : Type*) [Field k]
         (G : Type*) [Group G]
         (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra k 𝔤]
         (D : Type*) [Ring D] [Algebra k D]

structure GEquivQCohSheaf
    (M : Type*) [AddCommGroup M] [Module k M] where
  groupAction : G →* (M ≃ₗ[k] M)

structure WeaklyEquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends GEquivQCohSheaf k G M where
  groupAction_DLinear : ∀ (g : G) (d : D) (m : M),
    groupAction g (d • m) = d • (groupAction g m)

structure EquivDModule
    (M : Type*) [AddCommGroup M] [Module k M] [Module D M]
    extends WeaklyEquivDModule k G D M where
  lieToD : 𝔤 →ₗ⁅k⁆ D
  lieAction_phi : 𝔤 →ₗ[k] Module.End k M
  actions_agree : ∀ (x : 𝔤) (v : M), lieAction_phi x v = (lieToD x) • v

end Equivariant
end DModulesII
