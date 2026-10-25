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
import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part3


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


noncomputable def hexInfra_witnessDispBridge : HexBridge :=
  hexInfra_dispBridgeOfContent 0 [(-1 : ℤ)] (by simp)
    (by rw [hexInfra_floor_disp_singleRight]; exact one_pos)

end StatMech.Universality
