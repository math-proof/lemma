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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part20


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_truncatedTwoHalfData_isEmpty :
    IsEmpty (HLHRTruncatedTwoHalfData 0 0 2) := by
  constructor
  intro H
  apply hlhr_no_unaugmented_split_singleLeft
  exact ⟨H.lower hlhr_singleLeft_Dn, H.upper hlhr_singleLeft_Dn,
    H.reconstruct hlhr_singleLeft_Dn,
    H.lower_halfSpace hlhr_singleLeft_Dn,
    H.upper_halfSpace hlhr_singleLeft_Dn⟩

end StatMech.Universality
