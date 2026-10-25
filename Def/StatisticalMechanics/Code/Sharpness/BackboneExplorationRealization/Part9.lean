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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part7
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


noncomputable def kernel (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hresum : LocalDomainResummation β J) :
    shb_ExplorationKernel (shb_BackboneExplorationDomain V)
      (shb_AmbientSegment V) where
  exploration := exploration
  amplitude := amplitude β J
  amplitude_nonneg := amplitude_nonneg β J hβ hJ
  amplitude_antitone := amplitude_antitone_of_domainResummation β J hresum
  advance_mono := advance_mono

end shb_BackboneExplorationDomain


def shb_segmentCut (H : SimpleGraph V) [DecidableRel H.Adj]
    (s : shb_AmbientSegment V)
    (e : H.edgeFinset) : Prop :=
  e.1 ∈ s.edgeSet

end
end StatMech.Sharpness
