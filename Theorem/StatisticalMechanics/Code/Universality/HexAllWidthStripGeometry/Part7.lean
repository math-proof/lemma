/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part8


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWStart_mem_mids (T L : ℕ) (hT : 0 < T) :
    hexAWStart ∈ hexAWMids T L := by
  rw [hexAWMids, Finset.mem_biUnion]
  refine ⟨hexAWOrigin T L hT, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, hexAWMid_origin_zero⟩


end
end StatMech.Universality
