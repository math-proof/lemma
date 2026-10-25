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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part10
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_segmentRho_eq_num_div
    (β : ℝ) (J : Sym2 V → ℝ) (d : shb_ExplorationDomain V)
    (s : shb_ExplorationSegment V) :
    shb_BackboneExplorationDomain.amplitude β J d s =
      shb_segmentNum β J d s / currentSum d.graph β J ∅ := by
  letI : DecidableRel d.graph.Adj := Classical.decRel _
  by_cases hs : s ∈ d.active
  · rw [shb_BackboneExplorationDomain.amplitude, if_pos hs,
      shb_segmentNum, dif_pos hs]
    unfold shb_segmentRho shb_rhoSupport
    rw [dif_pos (d.active_supported s hs)]
  · simp [shb_BackboneExplorationDomain.amplitude, shb_segmentNum, hs]


end
end StatMech.Sharpness
