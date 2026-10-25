/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part22


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_bridge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : {p // p ∈ hlhd_intervals ts hleg}) : HexBridge where
  width := hlhd_width ts hleg p.1
  width_pos := by
    apply hlhd_width_pos_of_span_pos ts hleg p.1
    exact hlhd_spans_pos ts hleg hhalf _ (by
      simpa [hlhd_spans, hlhr_intervalSpans] using
        List.mem_map_of_mem p.2)
  content := hlhr_intervalContent ts p.1
  content_ne := by
    obtain ⟨hp12, hp2len⟩ := hlhd_interval_bounds ts hleg hhalf p.1 p.2
    unfold hlhr_intervalContent
    have htake : p.1.2 - p.1.1 ≤ (ts.drop p.1.1).length := by
      simp only [List.length_drop]
      omega
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le htake] at hlen
    simp only [List.length_nil] at hlen
    omega

noncomputable def hlhd_bridgeList (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) : List HexBridge :=
  (hlhd_intervals ts hleg).attach.map (hlhd_bridge ts hleg hhalf)

end
end StatMech.Universality
