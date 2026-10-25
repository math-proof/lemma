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
import Structure.v1.Atlas.LieGroups.code.DModulesII.Part3
open CategoryTheory


namespace DModulesII

section DAffine

universe u_dxmod u_aag

variable (k : Type u_aag) [Field k]
         (K : Type u_aag) [Group K]
         (𝔨 : Type u_aag) [LieRing 𝔨] [LieAlgebra k 𝔨]
         (D : Type u_aag) [Ring D] [Algebra k D]

attribute [instance] BBLocalizationData.grpG BBLocalizationData.grpK
  BBLocalizationData.lieRing_𝔤 BBLocalizationData.lieAlg_𝔤
  BBLocalizationData.lieRing_𝔨 BBLocalizationData.lieAlg_𝔨
  BBLocalizationData.lieRing_𝔥 BBLocalizationData.lieAlg_𝔥
  BBLocalizationData.ring_D BBLocalizationData.alg_D
  BBLocalizationData.add_𝔥star BBLocalizationData.mod_𝔥star
  BBLocalizationData.isNoetherian_D

def BBLocalizationData.IsAntidominant {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : Prop :=
  ∀ α ∈ bd.posRoots, ∀ hv : bd.𝔥, ¬(∃ n : ℕ, n > 0 ∧ (bd.duality hv) (bd.lam - n • α) = 0)

def IsKEquivDModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M =>
  let _instk : Module k' M := Module.compHom M (algebraMap k' bd.D)
  ∃ (groupAction : bd.K →* (M ≃ₗ[k'] M)),
    (∀ (g : bd.K) (d : bd.D) (m : M), groupAction g (d • m) = d • (groupAction g m)) ∧
    ∃ (lieAction : bd.𝔨 →ₗ[k'] Module.End k' M),
      (∀ (x y : bd.𝔨), lieAction ⁅x, y⁆ =
        lieAction x * lieAction y - lieAction y * lieAction x) ∧
      (∀ (x : bd.𝔨) (v : M), lieAction x v = (bd.lieToD (bd.ι𝔨 x)) • v)

def IsGKModBB {k' : Type u_aag} [Field k']
    (bd : BBLocalizationData k') : ObjectProperty (ModuleCat.{u_aag} bd.D) := fun M => by
  letI : Module k' M := Module.compHom M (algebraMap k' bd.D)
  exact ∃ (groupAct : bd.K →* (M ≃ₗ[k'] M))
    (_ : ∀ (m : M), (Submodule.span k' (Set.range (fun g => (groupAct g : M ≃ₗ[k'] M) m))).FG)
    (lieAct : bd.𝔨 →ₗ[k'] Module.End k' M),

    (∀ (x : bd.𝔨) (v : M), lieAct x v = (bd.lieToD (bd.ι𝔨 x)) • v) ∧

    (∀ (g : bd.K) (x : bd.𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (bd.Ad_K g x)) v)

end DAffine
end DModulesII
