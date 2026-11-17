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
public import Class.v1.Atlas.LieGroups.code.DModulesII.Part3

@[expose] public section

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
