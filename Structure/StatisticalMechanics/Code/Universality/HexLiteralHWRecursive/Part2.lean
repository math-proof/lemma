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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part19


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HLHRTwoHalfSpaceSplit (a : ℂ) (h0 : ℤ) (ts : List ℤ) where
  lower : List ℤ
  upper : List ℤ
  lowerHead : ℤ
  upperHead : ℤ
  reconstruct : ts = lower ++ upper
  lower_halfSpace : HLHRLiteralHalfSpace lowerHead lower
  upper_halfSpace : HLHRLiteralHalfSpace upperHead upper


structure HLHRTruncatedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) where
  lower : hhc_Dn a h0 N → List ℤ
  upper : hhc_Dn a h0 N → List ℤ
  reconstruct : ∀ d, d.1 = lower d ++ upper d
  lower_legal : ∀ d, (ofTurns 0 0 (lower d)).IsLegalSAW
  upper_legal : ∀ d, (ofTurns 0 0 (upper d)).IsLegalSAW
  lower_halfSpace : ∀ d, HLHRLiteralHalfSpace 0 (lower d)
  upper_halfSpace : ∀ d, HLHRLiteralHalfSpace 0 (upper d)


end StatMech.Universality
