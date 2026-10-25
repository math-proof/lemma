/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexAWStart_mem_hexCSMids (T L : ℕ) (hT : 0 < T) :
    hexAWStart ∈ hexCSMids T L := by
  rw [hexCSMids, Finset.mem_biUnion]
  refine ⟨hexCSOrigin T L hT, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, hexAWMid_origin_zero⟩

end
end StatMech.Universality
