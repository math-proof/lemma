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
import Def.v1.Atlas.LieGroups.code.KFinite


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

theorem isKFinite_zero (π : ContinuousRep G V) (K : Subgroup G) :
    IsKFinite π K (0 : V) := by
  unfold IsKFinite
  have hrng : Set.range (fun k : K => (π.toMonoidHom k) (0 : V)) = {0} := by
    ext x; simp
  rw [hrng, Submodule.span_singleton_eq_bot.mpr rfl]
  exact Module.Finite.bot ℂ V

theorem isKFinite_add (π : ContinuousRep G V) (K : Subgroup G) (v w : V)
    (hv : IsKFinite π K v) (hw : IsKFinite π K w) :
    IsKFinite π K (v + w) := by
  unfold IsKFinite at *
  set Sv := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))
  set Sw := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) w))
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) (v + w))) ≤ Sv ⊔ Sw := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp only [map_add]
    exact Submodule.add_mem_sup
      (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.subset_span ⟨k, rfl⟩)
  have : FiniteDimensional ℂ ↥(Sv ⊔ Sw) := Submodule.finite_sup Sv Sw
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

theorem isKFinite_smul (π : ContinuousRep G V) (K : Subgroup G)
    (c : ℂ) (v : V) (hv : IsKFinite π K v) :
    IsKFinite π K (c • v) := by
  unfold IsKFinite at *
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) (c • v))) ≤
      Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    simp only [map_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

end ContinuousRep
end
