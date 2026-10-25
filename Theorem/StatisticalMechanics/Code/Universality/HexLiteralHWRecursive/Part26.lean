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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part25


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


theorem contentPair_injective (H : HLHRAugmentedTwoHalfData a h0 N) :
    Function.Injective H.contentPair := by
  intro d e hpair
  apply H.listPair_injective
  apply Prod.ext
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.1)
      hpair
    simpa [contentPair] using h
  · have h := congrArg
      (fun p : HexHWContentHalf × HexHWContentHalf => hhc_halfTurns p.2)
      hpair
    simpa [contentPair] using h


theorem source_weight_factor (H : HLHRAugmentedTwoHalfData a h0 N)
    (x : ℝ) (hx : 0 < x) (d : hhc_Dn a h0 N) :
    x ^ d.1.length = (x ^ 2)⁻¹ *
      (hhc_halfWeight x (H.lowerHalf d) *
        hhc_halfWeight x (H.upperHalf d)) := by
  rw [hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow,
    H.lowerHalf_turns, H.upperHalf_turns]
  exact hexHW_two_overcount_pow_factor x hx _ _ _ (H.length_add_two d)


end HLHRAugmentedTwoHalfData
end StatMech.Universality
