/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part8
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


theorem toPath_mapLe
    {H K : SimpleGraph V} (hHK : H ≤ K) (s : shb_AmbientSegment V)
    (hH : s.Supported H) (hK : s.Supported K) :
    shb_pathMapLe hHK (s.toPath H hH) = s.toPath K hK := by
  apply Subtype.ext
  apply Walk.support_injective
  change (Walk.mapLe hHK (s.toPath H hH).1).support =
    (s.toPath K hK).1.support
  rw [Walk.support_mapLe_eq_support]
  change (s.2.2.1.transfer H hH).support = (s.2.2.1.transfer K hK).support
  rw [Walk.support_transfer, Walk.support_transfer]

theorem amplitude_antitone_of_domainResummation
    (β : ℝ) (J : Sym2 V → ℝ) (hresum : LocalDomainResummation β J)
    {d k : shb_BackboneExplorationDomain V} (hdk : d ≤ k)
    (s : shb_AmbientSegment V) :
    amplitude β J k s ≤ amplitude β J d s := by
  by_cases hs : s ∈ d.active
  · have hsk : s ∈ k.active := by simpa [← hdk.2] using hs
    letI : DecidableRel d.graph.Adj := Classical.decRel _
    letI : DecidableRel k.graph.Adj := Classical.decRel _
    simp only [amplitude, hs, hsk, if_true]
    let hd := d.active_supported s hs
    let hk := k.active_supported s hsk
    unfold shb_segmentRho
    rw [dif_pos hd, dif_pos hk]
    have hp3 := shb_P3_support_of_domainResummation
      d.graph k.graph hdk.1 β J (s.toPath d.graph hd) (hresum d k hdk s hs)
    rw [toPath_mapLe hdk.1 s hd hk] at hp3
    exact hp3
  · have hsk : s ∉ k.active := by simpa [← hdk.2] using hs
    simp [amplitude, hs, hsk]


end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
