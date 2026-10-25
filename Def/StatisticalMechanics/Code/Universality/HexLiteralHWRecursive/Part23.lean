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
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


def lower (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : List ℤ :=
  H.lowerBoundary d :: H.lowerCore d


def upper (H : HLHRAugmentedTwoHalfData a h0 N)
    (d : hhc_Dn a h0 N) : List ℤ :=
  H.upperBoundary d :: H.upperCore d

end HLHRAugmentedTwoHalfData
end StatMech.Universality
