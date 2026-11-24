module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def HLHRAhead (f : ℕ → ℝ) (up : Bool) (lo hi : ℕ) : Prop :=
  ∀ j, lo < j → j ≤ hi →
    hlhr_signed up (f lo) < hlhr_signed up (f j)


end StatMech.Universality
