/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part3
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_fkRectZeroTurnCutRemainderComponents
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)) :
    C ∈ fkRectZeroTurnCutRemainderComponents R omega ↔
      FKMedialTurningFiber.canonicalComponentTurn
          (fkRectConfigurationToMedialPairing R omega) C = 0 ∧
        ¬ FKRectMedialHitsHorizontalSeam R omega C := by
  classical
  simp [fkRectZeroTurnCutRemainderComponents]

end
end StatMech.FrontierD
