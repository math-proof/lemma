/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Instance.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphConfigurationExtend_configurationGraphEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectGraphConfigurationExtend R
        (fkRectConfigurationGraphEquiv R omega) =
      fkRectFullGraphConfiguration R omega := by
  funext e
  by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
  · simp [fkRectGraphConfigurationExtend, fkRectFullGraphConfiguration,
      fkRectConfigurationGraphEquiv, he]
  · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R omega he]
    simp [fkRectGraphConfigurationExtend, he]


end
end StatMech.FrontierD
