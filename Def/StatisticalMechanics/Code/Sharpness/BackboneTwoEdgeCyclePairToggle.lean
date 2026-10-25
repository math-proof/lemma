/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCyclePairToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCyclePairToggle
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCyclePairToggle

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open BackboneTwoEdgeCycleObstruction

open FluxEdgeCopy

def suffixCopy : Copy domain.graph superposition :=
  ⟨suffixEdge, ⟨0, by simp⟩⟩


end BackboneTwoEdgeCyclePairToggle
end
end StatMech.Sharpness
