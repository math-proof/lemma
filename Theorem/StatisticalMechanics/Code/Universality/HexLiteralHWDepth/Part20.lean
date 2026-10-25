/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part18


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_spans_pairwise (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    (hlhd_spans ts hleg).Pairwise (· > ·) := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_spans, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · exact (hlhr_intervalSpans_ordered (hlhd_height ts hleg) ts.length
      ts.length 0 true (List.length_pos_iff.mpr hempty)
      (hlhd_halfSpace_ahead ts hleg hhalf)).1

theorem hlhd_spans_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    ∀ w ∈ hlhd_spans ts hleg, 0 < w := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_spans, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · exact (hlhr_intervalSpans_ordered (hlhd_height ts hleg) ts.length
      ts.length 0 true (List.length_pos_iff.mpr hempty)
      (hlhd_halfSpace_ahead ts hleg hhalf)).2.1


end
end StatMech.Universality
