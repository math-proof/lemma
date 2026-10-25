/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part6


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSDomainInteriorPairing_interior_sub
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomainInteriorPairing T L hT hlocal).interior ⊆
      (hexCSDomain T L hT hlocal).incidences := by
  intro e he
  unfold HexDomain.incidences
  rw [Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp [hexCSDomain], rfl⟩

theorem hexCSDomain_incidences_eq
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT) :
    (hexCSDomain T L hT hlocal).incidences = hexCSIncidences T L := by
  ext e
  simp [HexDomain.incidences, hexCSIncidences, hexCSDomain]


end
end StatMech.Universality
