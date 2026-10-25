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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part4
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_segmentRho_nonneg
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (H : SimpleGraph V) (s : shb_AmbientSegment V) :
    0 ≤ shb_segmentRho β J H s := by
  letI : DecidableRel H.Adj := Classical.decRel _
  unfold shb_segmentRho
  split
  · apply div_nonneg
    · exact shb_backboneNumSupport_nonneg H β J hβ hJ _ _ _
    · exact le_of_lt (StatMech.Ising.acr_currentSum_empty_pos H β J)
  · exact le_rfl


end
end StatMech.Sharpness
