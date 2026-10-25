/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part16


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_literalWidths_pos (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    ∀ T ∈ hlhr_literalWidths ts, 0 < T := by
  intro T hT
  simp only [hlhr_literalWidths, List.mem_map] at hT
  obtain ⟨p, hp, rfl⟩ := hT
  apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p
  exact hlhr_literalSpans_pos 0 ts hhalf
    (hlhr_intervalSpan (hlhr_height 0 ts) p) (by
      simpa [hlhr_literalSpans, hlhr_intervalSpans] using
        List.mem_map_of_mem hp)


theorem hlhr_literalWidths_pairwise (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    (hlhr_literalWidths ts).Pairwise (· > ·) := by
  have hreal := hlhr_literalSpans_pairwise 0 ts hhalf
  have hintervals : (hlhr_literalIntervals 0 ts).Pairwise
      (fun p q => hlhr_intervalSpan (hlhr_height 0 ts) p >
        hlhr_intervalSpan (hlhr_height 0 ts) q) := by
    unfold hlhr_literalSpans hlhr_intervalSpans at hreal
    exact List.pairwise_map.mp hreal
  unfold hlhr_literalWidths
  rw [List.pairwise_map]
  exact hintervals.imp (fun hpq =>
    hlhr_latticeWidth_gt_of_span_gt ts hleg.1 _ _ hpq)


end StatMech.Universality
