/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part5
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part12
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (ιV : Vin → Vout)


variable {Gin Gout ιV}

variable (Gin Gout ιV)

variable (bdryOut : Vout → Prop) [DecidablePred bdryOut]


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

theorem ocd_fullComponentMap_inl_mk (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) (x : Vin) :
    ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ
        (Sum.inl ((ocd_innerGraph Gin Gout ιV bdryOut ω ψ).connectedComponentMk x))
      = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk (ιV x) := rfl

theorem ocd_fullComponentMap_inr_mk (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) (v : Vout)
    (hv : ocd_IsOutsideOnly Gout ιV bdryOut ψ
        ((ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v)) :
    ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ
        (Sum.inr ⟨(ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk v, hv⟩)
      = (ocd_fullGraph Gout ιV bdryOut ω ψ).connectedComponentMk v := rfl

theorem ocd_fullComponentMap_injective (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    Function.Injective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
  rintro (c₁ | ⟨c₁, hc₁⟩) (c₂ | ⟨c₂, hc₂⟩) h
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inl_mk, ConnectedComponent.eq] at h
    exact congrArg Sum.inl
      (ConnectedComponent.eq.mpr (ocd_innerGraph_reachable_of_fullGraph hι hadjm ω ψ h))
  · induction c₁ using ConnectedComponent.ind with | _ x₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x₁) v₂ :=
      ConnectedComponent.eq.mp h
    have hv₂ : ocd_OutsideOnly Gout ιV bdryOut ψ v₂ := (ocd_isOutsideOnly_mk ψ v₂).mp hc₂
    have : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₂ (ιV x₁) :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₂ hreach.symm
    exact absurd ⟨x₁, rfl⟩ (hv₂ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ x₂ =>
    rw [ocd_fullComponentMap_inl_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x₂) v₁ :=
      ConnectedComponent.eq.mp h.symm
    have hv₁ : ocd_OutsideOnly Gout ιV bdryOut ψ v₁ := (ocd_isOutsideOnly_mk ψ v₁).mp hc₁
    have : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₁ (ιV x₂) :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₁ hreach.symm
    exact absurd ⟨x₂, rfl⟩ (hv₁ _ this)
  · induction c₁ using ConnectedComponent.ind with | _ v₁ =>
    induction c₂ using ConnectedComponent.ind with | _ v₂ =>
    rw [ocd_fullComponentMap_inr_mk, ocd_fullComponentMap_inr_mk] at h
    have hreach : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable v₁ v₂ := ConnectedComponent.eq.mp h
    have hv₁ : ocd_OutsideOnly Gout ιV bdryOut ψ v₁ := (ocd_isOutsideOnly_mk ψ v₁).mp hc₁
    have hout : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable v₁ v₂ :=
      ocd_outsideGraph_reachable_of_fullGraph_outsideOnly hι ω ψ hv₁ hreach
    refine congrArg Sum.inr (Subtype.ext ?_)
    exact ConnectedComponent.sound hout

theorem ocd_fullComponentMap_surjective (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    Function.Surjective (ocd_fullComponentMap Gin Gout ιV bdryOut hι hadjm ω ψ) := by
  classical
  intro C
  induction C using ConnectedComponent.ind with | _ u =>
  by_cases hu : ∃ w, ocd_IsInnerVert ιV w ∧ (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable u w
  · obtain ⟨w, hw, hreach⟩ := hu
    obtain ⟨x, rfl⟩ := hw
    refine ⟨Sum.inl ((ocd_innerGraph Gin Gout ιV bdryOut ω ψ).connectedComponentMk x), ?_⟩
    rw [ocd_fullComponentMap_inl_mk]
    exact ConnectedComponent.sound hreach.symm
  · have hOut : ocd_OutsideOnly Gout ιV bdryOut ψ u := by
      intro v hv hinner
      exact hu ⟨v, hinner, hv.mono (ocd_outsideGraph_le_fullGraph ω ψ)⟩
    refine ⟨Sum.inr ⟨(ocd_outsideGraph Gout ιV bdryOut ψ).connectedComponentMk u,
      (ocd_isOutsideOnly_mk ψ u).mpr hOut⟩, ?_⟩
    rw [ocd_fullComponentMap_inr_mk]


end FK
end StatMech
