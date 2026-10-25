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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part16


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_literalBridge (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts)
    (p : {p // p ∈ hlhr_literalIntervals 0 ts}) : HexBridge where
  width := hlhr_latticeWidth ts p.1
  width_pos := by
    apply hlhr_latticeWidth_pos_of_span_pos ts hleg.1 p.1
    exact hlhr_literalSpans_pos 0 ts hhalf
      (hlhr_intervalSpan (hlhr_height 0 ts) p.1) (by
        simpa [hlhr_literalSpans, hlhr_intervalSpans] using
          List.mem_map_of_mem p.2)
  content := hlhr_intervalContent ts p.1
  content_ne := by
    obtain ⟨hp12, hp2len⟩ :=
      hlhr_literalInterval_bounds 0 ts hhalf p.1 p.2
    unfold hlhr_intervalContent
    have hdle : p.1.2 - p.1.1 ≤ (ts.drop p.1.1).length := by
      simp only [List.length_drop]
      omega
    intro hnil
    have hlen := congrArg List.length hnil
    rw [List.length_take_of_le hdle] at hlen
    simp only [List.length_nil] at hlen
    omega

end StatMech.Universality
