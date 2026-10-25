/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part6
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem fkRectForceEdgesOpen_of_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∈ I) :
    fkRectForceEdgesOpen R I omega a = true := by
  simp [fkRectForceEdgesOpen, ha]

@[simp] theorem fkRectForceEdgesOpen_of_not_mem
    (R : FKRectTorus) {I : Finset R.EdgeIndex}
    (omega : R.Configuration) {a : R.EdgeIndex} (ha : a ∉ I) :
    fkRectForceEdgesOpen R I omega a = omega a := by
  simp [fkRectForceEdgesOpen, ha]


end
end StatMech.FrontierD
