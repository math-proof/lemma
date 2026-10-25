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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part7


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlhr_height (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℝ :=
  hexW2_partialDisp h0 ts k


def HLHRLiteralHalfSpace (h0 : ℤ) (ts : List ℤ) : Prop :=
  ∀ k, 0 < k → k ≤ ts.length → hlhr_height h0 ts 0 < hlhr_height h0 ts k


end StatMech.Universality
