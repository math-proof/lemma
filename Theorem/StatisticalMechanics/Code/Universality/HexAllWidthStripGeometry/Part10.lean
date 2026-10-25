/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Instance.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAWIsInterior_reflect_iff {T L : ℕ}
    (e : HexAWIncidence T L) :
    hexAWIsInterior (hexAWReflectIncidence e) ↔ hexAWIsInterior e := by
  unfold hexAWIsInterior hexAWReflectIncidence hexAWReflectVertex
  change hexAWNeighbor (hexAWReflectCoord e.vtx.1)
      (hexAWReflectEdge e.edge) ∈ hexAWVertexSet T L ↔
    hexAWNeighbor e.vtx.1 e.edge ∈ hexAWVertexSet T L
  rw [← hexAWReflectCoord_neighbor, hexAWVertexSet_reflect_iff]


end
end StatMech.Universality
