/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part5


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem HexEndpointLocalCrossing.loopLength_pos
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c) : 0 < C.loopLength := by
  simpa only [HexEndpointLocalCrossing.loopLength] using
    (Nat.sub_pos_of_lt C.index_lt)


end
end StatMech.Universality
