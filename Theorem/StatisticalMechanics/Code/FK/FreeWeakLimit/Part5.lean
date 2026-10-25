/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeWeakLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Foundations.WeakConvergence
import Def.StatisticalMechanics.Code.FK.FreeWeakLimit.Part5
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK

variable {d : ℕ}


theorem fullComponentMapFree_inl_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (x : boxVerts d n) :
    fullComponentMapFree d n ω ψ (Sum.inl ((innerGraphFree d n ω ψ).connectedComponentMk x))
      = (fullGraphFree d n ω ψ).connectedComponentMk (boxVertIncl d n x) := rfl

theorem fullComponentMapFree_inr_mk (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (v : boxVerts d (n+1))
    (hv : IsOutsideOnlyFree d n ψ ((outsideOpenGraph d n ψ).connectedComponentMk v)) :
    fullComponentMapFree d n ω ψ
        (Sum.inr ⟨(outsideOpenGraph d n ψ).connectedComponentMk v, hv⟩)
      = (fullGraphFree d n ω ψ).connectedComponentMk v := rfl


theorem fullComponentMapFree_injective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Injective (fullComponentMapFree d n ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (innerGraphFree_reachable_of_fullGraphFree d n ω ψ h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x₁) v₂ :=
      ConnectedComponent.eq.mp h
    have hv₂ : OutsideOnlyFree d n ψ v₂ := (isOutsideOnlyFree_mk d n ψ v₂).mp hc₂
    have : (outsideOpenGraph d n ψ).Reachable v₂ (boxVertIncl d n x₁) :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₂ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₁) (hv₂ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [fullComponentMapFree_inl_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable (boxVertIncl d n x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : OutsideOnlyFree d n ψ v₁ := (isOutsideOnlyFree_mk d n ψ v₁).mp hc₁
    have : (outsideOpenGraph d n ψ).Reachable v₁ (boxVertIncl d n x₂) :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₁ hreach.symm
    exact absurd (isInnerVert_boxVertIncl d n x₂) (hv₁ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [fullComponentMapFree_inr_mk, fullComponentMapFree_inr_mk] at h
    have hreach : (fullGraphFree d n ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : OutsideOnlyFree d n ψ v₁ := (isOutsideOnlyFree_mk d n ψ v₁).mp hc₁
    have hout : (outsideOpenGraph d n ψ).Reachable v₁ v₂ :=
      outsideOpenGraph_reachable_of_fullGraphFree_outsideOnly d n ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout


theorem fullComponentMapFree_surjective (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    Function.Surjective (fullComponentMapFree d n ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, IsInnerVert d n w ∧ (fullGraphFree d n ω ψ).Reachable u w
  · obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := (isInnerVert_iff_range d n w).mp hw
    refine ⟨Sum.inl ((innerGraphFree d n ω ψ).connectedComponentMk x), ?_⟩
    rw [fullComponentMapFree_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · have hOut : OutsideOnlyFree d n ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (outsideOpenGraph_le_fullGraphFree d n ω ψ)⟩
    refine ⟨Sum.inr ⟨(outsideOpenGraph d n ψ).connectedComponentMk u,
      (isOutsideOnlyFree_mk d n ψ u).mpr hOut⟩, ?_⟩
    rw [fullComponentMapFree_inr_mk]


end FK
end StatMech
