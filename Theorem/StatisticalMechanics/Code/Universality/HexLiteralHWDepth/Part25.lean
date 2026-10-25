/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part23


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalMid_spec (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    hexInfra_midAccum hexAWStart 1
        ((hlhd_intervalEndpoint ts hleg hhalf p hp).take k.1) =
      hexAWMid (hlhd_intervalMidCoord ts hleg hhalf p hp k)
        (hlhd_intervalMidEdge ts hleg hhalf p hp k) ∧
    0 ≤ hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ∧
      hexAWBookRe2 (hlhd_intervalMidCoord ts hleg hhalf p hp k) ≤
        3 * hlhd_width ts hleg p := by
  unfold hlhd_intervalMidCoord hlhd_intervalMidEdge
  exact Classical.choose_spec (Classical.choose_spec
    (hlhd_intervalEndpoint_mid_incident_horizontal
      ts hleg hhalf p hp k.1 k.2))


end
end StatMech.Universality
