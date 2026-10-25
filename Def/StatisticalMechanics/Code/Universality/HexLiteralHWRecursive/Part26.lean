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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part26


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


noncomputable def lowerImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image H.lowerHalf


noncomputable def upperImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset HexHWContentHalf := by
  classical
  exact Finset.univ.image H.upperHalf


noncomputable def pairImage (H : HLHRAugmentedTwoHalfData a h0 N) :
    Finset (HexHWContentHalf × HexHWContentHalf) := by
  classical
  exact Finset.univ.image H.contentPair


end HLHRAugmentedTwoHalfData
end StatMech.Universality
