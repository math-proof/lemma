/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part8


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCSStartIncidence_mid (T L : ℕ) (hT : 0 < T) :
    hexAWMid (hexCSStartIncidence T L hT).vtx.1
      (hexCSStartIncidence T L hT).edge = hexAWStart :=
  hexAWMid_origin_zero

theorem hexCSStartIncidence_mem_boundary (T L : ℕ) (hT : 0 < T) :
    hexCSStartIncidence T L hT ∈ hexCSBoundaryIncidences T L := by
  apply hexCS_mem_boundary_of_classification
  left
  exact ⟨rfl, rfl, rfl⟩


end
end StatMech.Universality
