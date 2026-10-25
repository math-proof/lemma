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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part21


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRTruncatedTwoHalfData

theorem halves_reconstruct {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) (d : hhc_Dn a h0 N) :
    d.1 = hhc_halfTurns (H.lowerHalf d) ++ hhc_halfTurns (H.upperHalf d) := by
  unfold lowerHalf upperHalf
  rw [hlhr_contentHalf_turns, hlhr_contentHalf_turns]
  exact H.reconstruct d


end HLHRTruncatedTwoHalfData
end StatMech.Universality
