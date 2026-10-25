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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_randomCurrentExploration :
    shb_DynamicEdgeExploration (SimpleGraph V) (shb_AmbientSegment V) where
  edgeOrder := fun _ => Finset.univ.toList
  edgeOrder_nodup := fun _ => Finset.nodup_toList _
  advance := shb_explorationAdvance


noncomputable def shb_segmentRho
    (β : ℝ) (J : Sym2 V → ℝ) (H : SimpleGraph V)
    (s : shb_AmbientSegment V) : ℝ := by
  letI : DecidableRel H.Adj := Classical.decRel _
  exact if h : s.Supported H then
    shb_rhoSupport H β J s.1 s.2.1 (s.toPath H h)
  else 0


end
end StatMech.Sharpness
