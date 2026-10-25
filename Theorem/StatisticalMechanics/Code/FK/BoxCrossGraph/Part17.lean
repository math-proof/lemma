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
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part17
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossComponentEquivAddFun_inl_mk (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (x : boxVerts d n) :
    crossComponentEquivAddFun d n ω hD
        (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x))
      = (crossWiredGraphAdd d n ω D).connectedComponentMk (boxVertIncl d n x) := rfl

theorem crossComponentEquivAddFun_inr_mk (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (a : AnnulusVert d n) :
    crossComponentEquivAddFun d n ω hD
        (Sum.inr ((annulusSubgraph d n D).connectedComponentMk a))
      = (crossWiredGraphAdd d n ω D).connectedComponentMk a.1 := rfl


theorem crossComponentEquivAddFun_injective (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    Function.Injective (crossComponentEquivAddFun d n ω hD) := by
  rintro (c₁ | a₁) (c₂ | a₂) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inl_mk,
      ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (inner_reachable_of_crossWiredGraphAdd d n ω hD h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction a₂ using ConnectedComponent.ind with | _ b₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inr_mk] at h
    have h' : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x₁) b₂.1 :=
      ConnectedComponent.eq.mp h
    exact absurd
      (crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x₁) h') b₂.2
  · induction a₁ using ConnectedComponent.ind with | _ b₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [crossComponentEquivAddFun_inl_mk, crossComponentEquivAddFun_inr_mk] at h
    have h' : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x₂) b₁.1 :=
      ConnectedComponent.eq.mp h.symm
    exact absurd
      (crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x₂) h') b₁.2
  · induction a₁ using ConnectedComponent.ind with | _ b₁ =>
    induction a₂ using ConnectedComponent.ind with | _ b₂ =>
    rw [crossComponentEquivAddFun_inr_mk, crossComponentEquivAddFun_inr_mk,
      ConnectedComponent.eq] at h
    exact congrArg Sum.inr
      (ConnectedComponent.eq.mpr (annulus_reachable_of_crossWiredGraphAdd d n ω hD h))


theorem crossComponentEquivAddFun_surjective (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) :
    Function.Surjective (crossComponentEquivAddFun d n ω hD) := by
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : IsInnerVert d n u
  · refine ⟨Sum.inl ((innerWiredGraph d n ω).connectedComponentMk ⟨(u : Site d), hu⟩), ?_⟩
    rw [crossComponentEquivAddFun_inl_mk]
    apply ConnectedComponent.sound
    have : boxVertIncl d n ⟨(u : Site d), hu⟩ = u := by apply Subtype.ext; rfl
    rw [this]
  · exact ⟨Sum.inr ((annulusSubgraph d n D).connectedComponentMk ⟨u, hu⟩), rfl⟩


end FK
end StatMech
