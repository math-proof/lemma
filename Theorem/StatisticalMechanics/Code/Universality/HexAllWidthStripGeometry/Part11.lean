/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part12


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAW_mem_incidences {T L : ℕ}
    (e : HexAWIncidence T L) : e ∈ hexAWIncidences T L := by
  rw [hexAWIncidences, Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp, rfl⟩


end
end StatMech.Universality
