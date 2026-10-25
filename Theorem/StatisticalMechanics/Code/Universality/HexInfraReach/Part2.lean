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
import Def.StatisticalMechanics.Code.Universality.HexInfraReach.Part2


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


theorem hexInfra_reachesWidth_of_dispBridge (a : ℂ) (h0 : ℤ) (b : HexBridge)
    (hb : hexInfra_IsDispBridge h0 b) :
    hexWall3_ReachesWidth a h0 b.width b.content :=
  hexInfra_reachesWidth_of_last_re a h0 b.width b.content hb


theorem hexInfra_dispBridge_colDomination (a : ℂ) (h0 : ℤ) (b : HexBridge) (χ : ℝ)
    (hsummable hle_one) {x : ℝ}
    (hx0 : 0 ≤ x) (hχ : 0 < χ) (hxχ : x ≤ χ)
    (hb : hexInfra_IsDispBridge h0 b)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    x ^ (HexWalk.ofTurns a h0 b.content).numVertices
      ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x :=
  hexWall3_colDomination_uncond a h0 b χ hsummable hle_one hx0 hχ hxχ
    (hexInfra_reachesWidth_of_dispBridge a h0 b hb) hSAW


end StatMech.Universality
