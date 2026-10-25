/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexW3Link.Part2


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


noncomputable def hexW3_witnessBridge : HexBridge :=
  hexW3_anchor 0 hexWall3_witnessBridge
    (by change 0 < ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊
        rw [hexInfra_floor_disp_singleRight]; exact one_pos)

end StatMech.Universality
