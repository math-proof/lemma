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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part9


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_literalIntervals_reconstruct (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    hlhr_intervalTurns ts (hlhr_literalIntervals h0 ts) = ts := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalIntervals, hlhr_intervalsAux, hlhr_intervalTurns]
  · apply hlhr_intervalsAux_reconstruct (hlhr_height h0 ts) ts ts.length 0 true
      (by omega) (by omega)
    intro _
    exact hlhr_literalHalfSpace_ahead h0 ts hhalf


theorem hlhr_literalSpans_pairwise (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    (hlhr_literalSpans h0 ts).Pairwise (· > ·) := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalSpans, hlhr_literalIntervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · have hlen : 0 < ts.length := List.length_pos_iff.mpr hempty
    exact (hlhr_intervalSpans_ordered (hlhr_height h0 ts) ts.length
      ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf)).1


theorem hlhr_literalSpans_pos (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    ∀ w ∈ hlhr_literalSpans h0 ts, 0 < w := by
  by_cases hempty : ts = []
  · simp [hempty, hlhr_literalSpans, hlhr_literalIntervals,
      hlhr_intervalsAux, hlhr_intervalSpans]
  · have hlen : 0 < ts.length := List.length_pos_iff.mpr hempty
    exact (hlhr_intervalSpans_ordered (hlhr_height h0 ts) ts.length
      ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf)).2.1


end StatMech.Universality
