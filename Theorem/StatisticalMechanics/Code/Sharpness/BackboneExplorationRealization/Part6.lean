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
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part7
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


theorem amplitude_nonneg (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (d : shb_BackboneExplorationDomain V) (s : shb_AmbientSegment V) :
    0 ≤ amplitude β J d s := by
  unfold amplitude
  split
  · exact shb_segmentRho_nonneg β J hβ hJ d.graph s
  · exact le_rfl


end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
