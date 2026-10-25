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
import Def.v1.Atlas.LieGroups.code.DModulesII.Part5
open CategoryTheory


namespace DModulesII

section DAffine

universe u_dxmod u_aag

variable (k : Type u_aag) [Field k]
         (K : Type u_aag) [Group K]
         (𝔨 : Type u_aag) [LieRing 𝔨] [LieAlgebra k 𝔨]
         (D : Type u_aag) [Ring D] [Algebra k D]

structure BBLocalizationData (k' : Type u_aag) [Field k'] where
  G : Type u_aag
  [grpG : Group G]
  K : Type u_aag
  [grpK : Group K]
  iK : K →* G
  𝔤 : Type u_aag
  [lieRing_𝔤 : LieRing 𝔤]
  [lieAlg_𝔤 : LieAlgebra k' 𝔤]
  𝔨 : Type u_aag
  [lieRing_𝔨 : LieRing 𝔨]
  [lieAlg_𝔨 : LieAlgebra k' 𝔨]
  ι𝔨 : 𝔨 →ₗ⁅k'⁆ 𝔤
  𝔥 : Type u_aag
  [lieRing_𝔥 : LieRing 𝔥]
  [lieAlg_𝔥 : LieAlgebra k' 𝔥]
  ι𝔥 : 𝔥 →ₗ⁅k'⁆ 𝔤
  D : Type u_aag
  [ring_D : Ring D]
  [alg_D : Algebra k' D]
  lieToD : 𝔤 →ₗ⁅k'⁆ D
  𝔥star : Type u_aag
  [add_𝔥star : AddCommGroup 𝔥star]
  [mod_𝔥star : Module k' 𝔥star]
  duality : 𝔥 →ₗ[k'] 𝔥star →ₗ[k'] k'
  roots : Set 𝔥star
  posRoots : Set 𝔥star
  lam : 𝔥star
  FlagVariety : Type u_aag
  [isNoetherian_D : IsNoetherian D D]
  aag_K : IsAffineAlgebraicGroup K
  Ad_K : K →* (𝔨 ≃ₗ[k'] 𝔨)

end DAffine
end DModulesII
