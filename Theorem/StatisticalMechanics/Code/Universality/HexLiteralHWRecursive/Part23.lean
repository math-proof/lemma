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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part22


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRTruncatedTwoHalfData

theorem finite_partial_bound {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (∑ s ∈ H.contentDecomp.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.contentDecomp.upperImage, hhc_halfWeight x s) := by
  exact hhc_literal_partial_bound a h0 N H.lowerHalf H.upperHalf
    H.halves_reconstruct hx

end HLHRTruncatedTwoHalfData
end StatMech.Universality
