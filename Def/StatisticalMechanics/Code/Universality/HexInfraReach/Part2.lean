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
import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


def hexInfra_IsDispBridge (h0 : ℤ) (b : HexBridge) : Prop :=
  (b.width : ℝ) ≤ hexInfra_disp h0 b.content


end StatMech.Universality
