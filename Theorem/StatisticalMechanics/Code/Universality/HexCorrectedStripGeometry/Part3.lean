/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Abbrev.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCSOrigin_mem (T L : ℕ) (hT : 0 < T) :
    hexAWOriginCoord ∈ hexCSVertexSet T L := by
  rw [hexCS_mem_vertexSet_iff]
  simp [hexCSInStrip, hexAWOriginCoord, hexAWBookRe2,
    hexAWDepth, hexAWLong]
  omega

end
end StatMech.Universality
