/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhr_stripColumnRealization_zero (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    HLHRStripColumnRealization 0 ts hhalf where
  column := fun p _ => hlhr_latticeWidth ts p
  column_pos := by
    intro p hp
    apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p
    exact hlhr_literalSpans_pos 0 ts hhalf
      (hlhr_intervalSpan (hlhr_height 0 ts) p) (by
        simpa [hlhr_literalSpans, hlhr_intervalSpans] using
          List.mem_map_of_mem hp)
  span_strict := by
    intro p _ q _ hpq
    exact hlhr_latticeWidth_gt_of_span_gt ts hleg.1 p q hpq

end
end StatMech.Universality
