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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part5
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


noncomputable def exploration :
    shb_DynamicEdgeExploration (shb_BackboneExplorationDomain V)
      (shb_AmbientSegment V) where
  edgeOrder := fun d => d.active.toList
  edgeOrder_nodup := fun d => Finset.nodup_toList d.active
  advance := advance


noncomputable def amplitude (β : ℝ) (J : Sym2 V → ℝ)
    (d : shb_BackboneExplorationDomain V) (s : shb_AmbientSegment V) : ℝ :=
  if s ∈ d.active then shb_segmentRho β J d.graph s else 0

end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
