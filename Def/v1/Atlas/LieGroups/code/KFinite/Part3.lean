/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Theorem.v1.Atlas.LieGroups.code.KFinite.Part2


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def restrictSubgroup [IsTopologicalGroup G]
    (π : ContinuousRep G V) (K : Subgroup G) :
    ContinuousRep K V where
  toMonoidHom := π.toMonoidHom.comp K.subtype
  continuous_action :=
    π.continuous_action.comp
      (Continuous.prodMk (continuous_subtype_val.comp continuous_fst) continuous_snd)

def subrepresentation
    (π : ContinuousRep G V)
    (W : Submodule ℂ V) (hW : π.IsInvariantSubspace W) :
    ContinuousRep G W where
  toMonoidHom :=
  { toFun := fun g =>
    { toLinearMap :=
      { toFun := fun ⟨v, hv⟩ =>
          ⟨(π.toMonoidHom g) v, hW.invariant g v hv⟩
        map_add' := fun ⟨v₁, _⟩ ⟨v₂, _⟩ => by ext; simp [map_add]
        map_smul' := fun c ⟨v, _⟩ => by ext; simp [map_smul] }
      cont := by
        apply Continuous.subtype_mk
        exact (π.toMonoidHom g).continuous.comp continuous_subtype_val }
    map_one' := by ext ⟨v, _⟩; simp
    map_mul' := fun g h => by ext ⟨v, _⟩; simp }
  continuous_action := by
    apply Continuous.subtype_mk
    show Continuous (fun p : G × W => (π.toMonoidHom p.1) (p.2 : V))
    exact π.continuous_action.comp
      (Continuous.prodMk continuous_fst
        (continuous_subtype_val.comp continuous_snd))

def IsotypicComponent [IsTopologicalGroup G]
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G V) (K : Subgroup G)
    (σ : ContinuousRep K Wσ) :
    Submodule ℂ V :=
  sSup { W : Submodule ℂ V |
    ∃ (hW : (π.restrictSubgroup K).IsInvariantSubspace W),
      ((π.restrictSubgroup K).subrepresentation W hW).IsIrreducible ∧
      Nonempty (RepEquiv
        ((π.restrictSubgroup K).subrepresentation W hW) σ) }

end ContinuousRep
end
