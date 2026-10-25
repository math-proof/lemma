/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


noncomputable def hexW3_anchor (h0 : ℤ) (b : HexBridge)
    (hpos : 0 < ⌊hexInfra_disp h0 b.content⌋₊) : HexBridge :=
  hexInfra_dispBridgeOfContent h0 b.content b.content_ne hpos

end StatMech.Universality
