/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexCSInStrip_mem_coordBox (T L : ℕ) (c : HexAWCoord)
    (hc : hexCSInStrip T L c) : c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth, hexAWLong] at hc
  all_goals
    simp [hexAWCoordBox]
    omega

end
end StatMech.Universality
