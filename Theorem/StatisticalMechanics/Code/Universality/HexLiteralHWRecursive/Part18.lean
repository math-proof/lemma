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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part18


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_literalBridgeList_contents (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    ((hlhr_literalBridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
  have hr := hlhr_literalIntervals_reconstruct 0 ts hhalf
  unfold hlhr_literalBridgeList
  simpa [hlhr_intervalTurns] using hr

theorem hlhr_literalBridgeList_widths (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    (hlhr_literalBridgeList ts hleg hhalf).map HexBridge.width =
      hlhr_literalWidths ts := by
  unfold hlhr_literalBridgeList hlhr_literalWidths
  simp


theorem hlhr_literalBridgeList_strict (ts : List ℤ)
    (hleg : (ofTurns 0 0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace 0 ts) :
    StrictDecreasingWidths (hlhr_literalBridgeList ts hleg hhalf) := by
  unfold StrictDecreasingWidths
  have hw := hlhr_literalWidths_pairwise ts hleg hhalf
  rw [← hlhr_literalBridgeList_widths ts hleg hhalf] at hw
  simpa [List.pairwise_map] using hw


end StatMech.Universality
