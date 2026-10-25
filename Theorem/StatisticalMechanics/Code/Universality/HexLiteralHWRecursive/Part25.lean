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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part24


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


@[simp] theorem lowerHalf_turns (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.lowerHalf d) = H.lower d := by
  exact hlhr_contentHalf_turns _ (H.lower_legal d) (H.lower_halfSpace d)

@[simp] theorem upperHalf_turns (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (H.upperHalf d) = H.upper d := by
  exact hlhr_contentHalf_turns _ (H.upper_legal d) (H.upper_halfSpace d)


end HLHRAugmentedTwoHalfData
end StatMech.Universality
