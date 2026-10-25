/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

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
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.InducedBC.Part9
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem fullComponentMap_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (x : boxVerts d n) :
    fullComponentMap d n ω ψ (Sum.inl ((innerGraph d n ω ψ).connectedComponentMk x))
      = (fullGraph d n ω ψ).connectedComponentMk (boxVertIncl d n x) := rfl

theorem fullComponentMap_inr_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (v : boxVerts d (n+1))
    (hv : IsOutsideOnly d n ψ ((outsideGraph d n ψ).connectedComponentMk v)) :
    fullComponentMap d n ω ψ (Sum.inr ⟨(outsideGraph d n ψ).connectedComponentMk v, hv⟩)
      = (fullGraph d n ω ψ).connectedComponentMk v := rfl


theorem fullComponentMap_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Injective (fullComponentMap d n ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl (ConnectedComponent.eq.mpr (innerGraph_reachable_of_fullGraph d n ω ψ h))
  · 
    induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x₁) v₂ :=
      ConnectedComponent.eq.mp h
    
    have hv₂ : OutsideOnly d n ψ v₂ := (isOutsideOnly_mk d n ψ v₂).mp hc₂
    have : (outsideGraph d n ψ).Reachable v₂ (boxVertIncl d n x₁) :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₂ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₁) (hv₂ _ this)
  · 
    induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMap_inl_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable (boxVertIncl d n x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : OutsideOnly d n ψ v₁ := (isOutsideOnly_mk d n ψ v₁).mp hc₁
    have : (outsideGraph d n ψ).Reachable v₁ (boxVertIncl d n x₂) :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₁ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₂) (hv₁ _ this)
  · 
    induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMap_inr_mk, fullComponentMap_inr_mk] at h
    have hreach : (fullGraph d n ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : OutsideOnly d n ψ v₁ := (isOutsideOnly_mk d n ψ v₁).mp hc₁
    have hout : (outsideGraph d n ψ).Reachable v₁ v₂ :=
      outsideGraph_reachable_of_fullGraph_outsideOnly d n ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout


theorem fullComponentMap_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Surjective (fullComponentMap d n ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, IsInnerVert d n w ∧ (fullGraph d n ω ψ).Reachable u w
  · 
    obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := (isInnerVert_iff_range d n w).mp hw
    refine ⟨Sum.inl ((innerGraph d n ω ψ).connectedComponentMk x), ?_⟩
    rw [fullComponentMap_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · 
    have hOut : OutsideOnly d n ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (outsideGraph_le_fullGraph d n ω ψ)⟩
    refine ⟨Sum.inr ⟨(outsideGraph d n ψ).connectedComponentMk u, (isOutsideOnly_mk d n ψ u).mpr hOut⟩, ?_⟩
    rw [fullComponentMap_inr_mk]


end FK
end StatMech
