/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part19


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAWRightFixedIncidence_mem_boundary (k L : ℕ) (hk : 0 < k) :
    hexAWRightFixedIncidence k L hk ∈
      hexAWBoundaryIncidences (2 * k) L := by
  rw [hexAW_mem_boundary_iff]
  unfold hexAWIsInterior hexAWRightFixedIncidence
  rw [hexAW_mem_vertexSet_iff]
  simp [hexAWNeighbor, hexAWRightFixedCoord, hexAWInStrip,
    hexAWBookRe2, hexAWBookSqrt3Im2, hexAWDepth, hexAWLong,
    hexAWTrans]
  omega

@[simp] theorem hexAWRightFixedIncidence_reflect (k L : ℕ) (hk : 0 < k) :
    hexAWReflectIncidence (hexAWRightFixedIncidence k L hk) =
      hexAWRightFixedIncidence k L hk := by
  rw [hexAWReflectIncidence, hexAWRightFixedIncidence,
    HexIncidence.mk.injEq]
  exact ⟨by apply Subtype.ext; rfl, rfl⟩

end
end StatMech.Universality
