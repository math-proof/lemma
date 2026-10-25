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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part22


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRTruncatedTwoHalfData

noncomputable def contentDecomp {a : ℂ} {h0 : ℤ} {N : ℕ}
    (H : HLHRTruncatedTwoHalfData a h0 N) :
    HexHWContentDecomp (hhc_Dn a h0 N) :=
  hhc_literalDecomp a h0 N H.lowerHalf H.upperHalf H.halves_reconstruct


end HLHRTruncatedTwoHalfData
end StatMech.Universality
