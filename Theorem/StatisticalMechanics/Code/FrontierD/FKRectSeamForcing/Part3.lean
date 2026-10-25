/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectCutClosedConfiguration_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectCutClosedConfiguration R (fkRectForceCutClosed R omega) := by
  simp [FKRectCutClosedConfiguration]

theorem fkRectCutClosedConfiguration_iff
    (R : FKRectTorus) (eta : R.Configuration) :
    FKRectCutClosedConfiguration R eta ↔
      ∀ a ∈ fkRectTorusCutEdges R, eta a = false := by
  constructor
  · intro hclosed a ha
    rw [<- hclosed]
    exact fkRectForceCutClosed_of_mem R eta a ha
  · intro hclosed
    unfold FKRectCutClosedConfiguration
    funext a
    by_cases ha : a ∈ fkRectTorusCutEdges R
    · rw [fkRectForceCutClosed_of_mem R eta a ha, hclosed a ha]
    · rw [fkRectForceCutClosed_of_not_mem R eta a ha]


end
end StatMech.FrontierD
