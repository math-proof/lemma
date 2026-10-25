/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part3


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAWInStrip_mem_coordBox (T L : ℕ) (c : HexAWCoord)
    (hc : hexAWInStrip T L c) : c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexAWInStrip, hexAWBookRe2, hexAWBookSqrt3Im2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc
  all_goals
    simp [hexAWCoordBox]
    omega


@[simp] theorem hexAW_mem_vertexSet_iff (T L : ℕ) (c : HexAWCoord) :
    c ∈ hexAWVertexSet T L ↔ hexAWInStrip T L c := by
  constructor
  · intro hc
    exact (Finset.mem_filter.mp hc).2
  · intro hc
    exact Finset.mem_filter.mpr ⟨hexAWInStrip_mem_coordBox T L c hc, hc⟩


end
end StatMech.Universality
