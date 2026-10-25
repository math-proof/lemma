/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part24


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalEndpoint_mem_topAtWidth (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    HexCSTopWalkAtWidth (hlhd_width ts hleg p)
      (hlhd_interval_width_pos ts hleg hhalf p hp)
      (hlhd_intervalEndpoint ts hleg hhalf p hp) := by
  exact (hlhd_midpointColumnWalk ts hleg hhalf p hp).mem_topAtWidth
    (hlhd_interval_width_pos ts hleg hhalf p hp)

end
end StatMech.Universality
