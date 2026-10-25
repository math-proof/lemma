/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part21


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_bridgeList_widths (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    (hlhd_bridgeList ts hleg hhalf).map HexBridge.width =
      (hlhd_intervals ts hleg).map (hlhd_width ts hleg) := by
  unfold hlhd_bridgeList
  simp [hlhd_bridge]

theorem hlhd_bridgeList_contents (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ((hlhd_bridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
  simpa [hlhd_bridgeList, hlhd_bridge, Function.comp_def,
    hlhd_intervalTurns, hlhr_intervalTurns] using
    hlhd_intervals_reconstruct ts hleg hhalf

theorem hlhd_bridgeList_strict (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    StrictDecreasingWidths (hlhd_bridgeList ts hleg hhalf) := by
  have hreal := hlhd_spans_pairwise ts hleg hhalf
  have hintervals : (hlhd_intervals ts hleg).Pairwise
      (fun p q => hlhr_intervalSpan (hlhd_height ts hleg) p >
        hlhr_intervalSpan (hlhd_height ts hleg) q) := by
    unfold hlhd_spans hlhr_intervalSpans at hreal
    exact List.pairwise_map.mp hreal
  have hwidths :
      ((hlhd_intervals ts hleg).map (hlhd_width ts hleg)).Pairwise
        (· > ·) :=
    List.pairwise_map.mpr (hintervals.imp (fun hpq =>
      hlhd_width_gt_of_span_gt ts hleg _ _ hpq))
  rw [← hlhd_bridgeList_widths ts hleg hhalf] at hwidths
  simpa [StrictDecreasingWidths, List.pairwise_map] using hwidths


end
end StatMech.Universality
