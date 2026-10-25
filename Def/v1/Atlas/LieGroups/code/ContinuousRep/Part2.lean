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
import Structure.v1.Atlas.LieGroups.code.ContinuousRep.Part2


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

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

end ContinuousRep
end
