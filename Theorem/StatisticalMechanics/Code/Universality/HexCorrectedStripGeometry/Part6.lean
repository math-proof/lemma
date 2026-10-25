/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part6


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCS_mem_incidences {T L : ℕ} (e : HexCSIncidence T L) :
    e ∈ hexCSIncidences T L := by
  rw [hexCSIncidences, Finset.mem_image]
  exact ⟨(e.vtx, e.edge), by simp, rfl⟩

@[simp] theorem hexCS_mem_interior_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    e ∈ hexCSInteriorIncidences T L ↔ hexCSIsInterior e := by
  simp [hexCSInteriorIncidences]

@[simp] theorem hexCS_mem_boundary_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    e ∈ hexCSBoundaryIncidences T L ↔ ¬ hexCSIsInterior e := by
  simp [hexCSBoundaryIncidences]

end
end StatMech.Universality
