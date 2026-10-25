/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part3


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexCSInStrip_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexCSInStrip T L (hexAWReflectCoord c) ↔ hexCSInStrip T L c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> simp [hexCSInStrip, hexAWReflectCoord, hexAWBookRe2,
    hexAWDepth, hexAWLong, and_left_comm, and_comm] <;> omega

@[simp] theorem hexCSVertexSet_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexCSVertexSet T L ↔
      c ∈ hexCSVertexSet T L := by
  simp only [hexCS_mem_vertexSet_iff, hexCSInStrip_reflect_iff]

end
end StatMech.Universality
