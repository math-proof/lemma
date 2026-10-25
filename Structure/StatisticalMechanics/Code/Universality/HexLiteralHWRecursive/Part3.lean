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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part23


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HLHRAugmentedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) where
  lowerBoundary : hhc_Dn a h0 N → ℤ
  upperBoundary : hhc_Dn a h0 N → ℤ
  lowerCore : hhc_Dn a h0 N → List ℤ
  upperCore : hhc_Dn a h0 N → List ℤ
  decode : ℤ → List ℤ → ℤ → List ℤ → List ℤ
  decode_source : ∀ d,
    decode (lowerBoundary d) (lowerCore d)
      (upperBoundary d) (upperCore d) = d.1
  core_length : ∀ d,
    (lowerCore d).length + (upperCore d).length = d.1.length
  lower_legal : ∀ d,
    (ofTurns 0 0 (lowerBoundary d :: lowerCore d)).IsLegalSAW
  upper_legal : ∀ d,
    (ofTurns 0 0 (upperBoundary d :: upperCore d)).IsLegalSAW
  lower_halfSpace : ∀ d,
    HLHRLiteralHalfSpace 0 (lowerBoundary d :: lowerCore d)
  upper_halfSpace : ∀ d,
    HLHRLiteralHalfSpace 0 (upperBoundary d :: upperCore d)

end StatMech.Universality
