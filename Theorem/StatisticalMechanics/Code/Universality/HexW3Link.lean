/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexW3Link


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


@[simp] theorem hexW3_anchor_content (h0 : ℤ) (b : HexBridge) (hpos) :
    (hexW3_anchor h0 b hpos).content = b.content := rfl

@[simp] theorem hexW3_anchor_width (h0 : ℤ) (b : HexBridge) (hpos) :
    (hexW3_anchor h0 b hpos).width = ⌊hexInfra_disp h0 b.content⌋₊ := rfl


theorem hexW3_anchor_isDispBridge (h0 : ℤ) (b : HexBridge) (hpos)
    (hd : 0 ≤ hexInfra_disp h0 b.content) :
    hexInfra_IsDispBridge h0 (hexW3_anchor h0 b hpos) :=
  hexInfra_dispBridgeOfContent_isDispBridge h0 b.content b.content_ne hpos hd


theorem hexW3_anchor_reaches (a : ℂ) (h0 : ℤ) (b : HexBridge) (hpos)
    (hd : 0 ≤ hexInfra_disp h0 b.content) :
    hexWall3_ReachesWidth a h0 (hexW3_anchor h0 b hpos).width
      (hexW3_anchor h0 b hpos).content :=
  hexInfra_reachesWidth_of_dispBridge a h0 (hexW3_anchor h0 b hpos)
    (hexW3_anchor_isDispBridge h0 b hpos hd)


end StatMech.Universality
