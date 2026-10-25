/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

def shb_emptyActiveSingleEdgeDomain (x y : V) : shb_ExplorationDomain V where
  graph := shb_singleEdgeGraph x y
  active := ∅
  active_supported := by simp


def shb_singleEdgeFlux (x y : V) :
    (shb_emptyActiveSingleEdgeDomain x y).graph.edgeFinset -> Nat := fun _ => 1

end
end StatMech.Sharpness
