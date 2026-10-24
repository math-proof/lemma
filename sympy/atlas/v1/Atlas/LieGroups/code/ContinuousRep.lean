/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Sequences

noncomputable section

open scoped ComplexOrder

structure ContinuousRep
    (G : Type*) [Group G] [TopologicalSpace G]
    (V : Type*) [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] where
  toMonoidHom : G →* (V →L[ℂ] V)
  continuous_action : Continuous (fun p : G × V => (toMonoidHom p.1) p.2)

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

def ofElem (π : ContinuousRep G V) (g : G) : V →L[ℂ] V := π.toMonoidHom g

structure IsInvariantSubspace (π : ContinuousRep G V)
    (W : Submodule ℂ V) : Prop where
  isClosed : IsClosed (W : Set V)
  invariant : ∀ (g : G) (v : V), v ∈ W → (π.toMonoidHom g) v ∈ W

def IsIrreducible (π : ContinuousRep G V) : Prop :=
  ∀ (W : Submodule ℂ V), π.IsInvariantSubspace W → W = ⊥ ∨ W = ⊤

def directSum
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) :
    ContinuousRep G (V × W) where
  toMonoidHom :=
  { toFun := fun g => (π₁.toMonoidHom g).prodMap (π₂.toMonoidHom g)
    map_one' := by ext <;> simp
    map_mul' := fun g h => by ext <;> simp }
  continuous_action := by
    show Continuous (fun p : G × (V × W) =>
      ((π₁.toMonoidHom p.1) p.2.1, (π₂.toMonoidHom p.1) p.2.2))
    have h1 : Continuous (fun p : G × (V × W) => (π₁.toMonoidHom p.1) p.2.1) :=
      π₁.continuous_action.comp
        (by fun_prop : Continuous (fun p : G × (V × W) => (p.1, p.2.1)))
    have h2 : Continuous (fun p : G × (V × W) => (π₂.toMonoidHom p.1) p.2.2) :=
      π₂.continuous_action.comp
        (by fun_prop : Continuous (fun p : G × (V × W) => (p.1, p.2.2)))
    fun_prop

def IsUnitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (π : ContinuousRep G E) : Prop :=
  ∀ g : G,
    ContinuousLinearMap.adjoint (π.toMonoidHom g) * (π.toMonoidHom g) = 1 ∧
    (π.toMonoidHom g) * ContinuousLinearMap.adjoint (π.toMonoidHom g) = 1

def IsStronglyContinuous
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : G →* (V →L[ℂ] V)) : Prop :=
  ∀ v : V, Continuous (fun g => (π g) v)

structure RepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearMap : V →L[ℂ] W
  intertwines : ∀ g : G,
    toContinuousLinearMap.comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp toContinuousLinearMap

structure RepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearEquiv : V ≃L[ℂ] W
  intertwines : ∀ g : G,
    (toContinuousLinearEquiv : V →L[ℂ] W).comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp (toContinuousLinearEquiv : V →L[ℂ] W)

def RepEquiv.toRepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {π₁ : ContinuousRep G V} {π₂ : ContinuousRep G W}
    (e : RepEquiv π₁ π₂) : RepHom π₁ π₂ where
  toContinuousLinearMap := e.toContinuousLinearEquiv
  intertwines := e.intertwines

end ContinuousRep
