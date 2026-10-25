/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part7
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossComponentEquivFun_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (x : boxVerts d n) :
    crossComponentEquivFun d n ω (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x))
      = (crossWiredGraph d n ω).connectedComponentMk (boxVertIncl d n x) := rfl


theorem crossWiredGraph_reachable_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {v w : boxVerts d (n+1)}
    (hv : ¬ IsInnerVert d n v) (h : (crossWiredGraph d n ω).Reachable v w) : w = v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail u w hvu hadj ih =>
      exact absurd hadj (by rw [ih]; exact crossWiredGraph_not_adj_of_annulus d n ω hv w)


theorem crossComponentEquivFun_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    Function.Injective (crossComponentEquivFun d n ω) := by
  rintro (c₁ | v₁) (c₂ | v₂) h
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivFun_inl_mk, crossComponentEquivFun_inl_mk,
      ConnectedComponent.eq] at h
    have hreach := inner_reachable_of_crossWiredGraph d n ω h
    exact congrArg Sum.inl (ConnectedComponent.eq.mpr hreach)
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    rw [crossComponentEquivFun_inl_mk] at h
    have h' : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x₁) v₂.1 :=
      ConnectedComponent.eq.mp h
    exact absurd
      (crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x₁) h') v₂.2
  · 
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivFun_inl_mk] at h
    have h' : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x₂) v₁.1 :=
      ConnectedComponent.eq.mp h.symm
    exact absurd
      (crossWiredGraph_reachable_inner d n ω (isInnerVert_boxVertIncl d n x₂) h') v₁.2
  · 
    have h' : (crossWiredGraph d n ω).Reachable v₁.1 v₂.1 := ConnectedComponent.eq.mp h
    exact congrArg Sum.inr
      (Subtype.ext (crossWiredGraph_reachable_annulus d n ω v₁.2 h').symm)


theorem crossComponentEquivFun_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    Function.Surjective (crossComponentEquivFun d n ω) := by
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : IsInnerVert d n u
  · 
    refine ⟨Sum.inl ((innerWiredGraph d n ω).connectedComponentMk ⟨(u : Site d), hu⟩), ?_⟩
    rw [crossComponentEquivFun_inl_mk]
    apply ConnectedComponent.sound
    have : boxVertIncl d n ⟨(u : Site d), hu⟩ = u := by apply Subtype.ext; rfl
    rw [this]
  · 
    exact ⟨Sum.inr ⟨u, hu⟩, rfl⟩


end FK
end StatMech
