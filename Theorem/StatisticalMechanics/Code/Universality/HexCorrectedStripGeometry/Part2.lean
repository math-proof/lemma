/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part2


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCS_mem_vertexSet_iff (T L : ℕ) (c : HexAWCoord) :
    c ∈ hexCSVertexSet T L ↔ hexCSInStrip T L c := by
  constructor
  · exact fun hc => (Finset.mem_filter.mp hc).2
  · exact fun hc => Finset.mem_filter.mpr
      ⟨hexCSInStrip_mem_coordBox T L c hc, hc⟩

end
end StatMech.Universality
