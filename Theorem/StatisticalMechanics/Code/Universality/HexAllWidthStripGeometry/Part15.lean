/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part16


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAWInteriorPairingOfDomain_interior_sub {T L : ℕ}
    (D : HexDomain (HexAWVertex T L))
    (hpos : ∀ v, D.pos v = hexAWPos v.1)
    (hmid : ∀ v e, D.mid v e = hexAWMid v.1 e)
    (hvertices : ∀ v, v ∈ D.interiorVertices) :
    (hexAWInteriorPairingOfDomain D hpos hmid).interior ⊆ D.incidences := by
  intro e he
  unfold HexDomain.incidences
  rw [Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp [hvertices], rfl⟩


end
end StatMech.Universality
