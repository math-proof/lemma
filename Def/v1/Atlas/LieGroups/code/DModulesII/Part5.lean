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
import Class.v1.Atlas.LieGroups.code.DModulesII.Part3
open CategoryTheory


namespace DModulesII

section DAffine

universe u_dxmod u_aag

variable (k : Type u_aag) [Field k]
         (K : Type u_aag) [Group K]
         (𝔨 : Type u_aag) [LieRing 𝔨] [LieAlgebra k 𝔨]
         (D : Type u_aag) [Ring D] [Algebra k D]

def StrongKEquivDModPred (lieToD : 𝔨 →ₗ⁅k⁆ D) : ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (g : K) (d : D) (m : M), groupAct g (d • m) = d • (groupAct g m))
    (liePhi : 𝔨 →ₗ[k] Module.End k M)
    (_ : ∀ (x y : 𝔨), liePhi ⁅x, y⁆ = liePhi x * liePhi y - liePhi y * liePhi x),
    ∀ (x : 𝔨) (v : M), liePhi x v = (lieToD x) • v

def CompatibleKActionPred (lieToD : 𝔨 →ₗ⁅k⁆ D) (Ad : K →* (𝔨 ≃ₗ[k] 𝔨)) :
    ObjectProperty (ModuleCat.{u_aag} D) := fun M => by
  letI : Module k M := Module.compHom M (algebraMap k D)
  exact ∃ (groupAct : K →* (M ≃ₗ[k] M))
    (_ : ∀ (m : M), (Submodule.span k (Set.range (fun g => (groupAct g : M ≃ₗ[k] M) m))).FG)
    (lieAct : 𝔨 →ₗ[k] Module.End k M),

    (∀ (x : 𝔨) (v : M), lieAct x v = (lieToD x) • v) ∧


    (∀ (g : K) (x : 𝔨) (v : M),
      (groupAct g) ((lieAct x) ((groupAct g).symm v)) = (lieAct (Ad g x)) v)

end DAffine
end DModulesII
