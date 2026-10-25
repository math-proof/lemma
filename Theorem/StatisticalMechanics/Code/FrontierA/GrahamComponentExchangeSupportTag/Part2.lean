/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeSupportTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem componentExchangeSupportTag_injective
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    Function.Injective
      (componentExchangeSupportTag ends m j k l zero
        hloop hjk hkl hk0) := by
  classical
  intro d e hde
  have hP := congrArg (fun r => r.2.1.1) hde
  have hA := congrArg (fun r => r.2.2.1) hde
  apply Subtype.ext
  have hdsub : edgeComponent ends d.1 zero ⊆ d.1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hesub : edgeComponent ends e.1 zero ⊆ e.1 := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hdrecover : d.1 =
      (d.1 \ edgeComponent ends d.1 zero) ∪
        edgeComponent ends d.1 zero := by
    exact (Finset.sdiff_union_of_subset hdsub).symm
  have herecover : e.1 =
      (e.1 \ edgeComponent ends e.1 zero) ∪
        edgeComponent ends e.1 zero := by
    exact (Finset.sdiff_union_of_subset hesub).symm
  rw [hdrecover, herecover]
  dsimp only [componentExchangeSupportTag] at hP hA
  rw [hP, hA]


theorem card_leftRowSupportIndex_le_rightRowData
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero) :
    Fintype.card (leftRowSupportIndex ends m j k l zero) ≤
      Fintype.card (rightRowData ends m j k l zero) := by
  exact Fintype.card_le_of_injective
    (componentExchangeSupportTag ends m j k l zero hloop hjk hkl hk0)
    (componentExchangeSupportTag_injective
      ends m j k l zero hloop hjk hkl hk0)

end StatMech.GrahamGHS.FourColor
