/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectMedialLoopCanonicalVerticalFlux_eq_zero_of_not_hitsHorizontalSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C) :
    fkMedialLoopCanonicalVerticalFlux
        (fkRectConfigurationToMedialPairing R omega) C = 0 := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg]
  intro hcomponent
  exact havoid ⟨i, hcomponent⟩

end
end StatMech.FrontierD
