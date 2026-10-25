/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraReach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Def.StatisticalMechanics.Code.Universality.HexInfraReach.Part4


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


@[simp] theorem hexInfra_witnessDispBridge_width : hexInfra_witnessDispBridge.width = 1 := by
  unfold hexInfra_witnessDispBridge
  rw [hexInfra_dispBridgeOfContent_width, hexInfra_floor_disp_singleRight]

@[simp] theorem hexInfra_witnessDispBridge_content :
    hexInfra_witnessDispBridge.content = [(-1 : ℤ)] := rfl


theorem hexInfra_singleRight_isDispBridge :
    hexInfra_IsDispBridge 0 hexInfra_witnessDispBridge :=
  hexInfra_dispBridgeOfContent_isDispBridge 0 [(-1 : ℤ)] _ _
    (le_trans (by norm_num) hexInfra_disp_singleRight_ge_one)


theorem hexInfra_witnessDispBridge_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 hexInfra_witnessDispBridge.width
      hexInfra_witnessDispBridge.content :=
  hexInfra_reachesWidth_of_dispBridge a 0 hexInfra_witnessDispBridge
    hexInfra_singleRight_isDispBridge

end StatMech.Universality
