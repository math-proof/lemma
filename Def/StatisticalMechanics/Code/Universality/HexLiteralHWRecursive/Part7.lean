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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part6


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def hlhr_intervalContent (ts : List ℤ) (p : ℕ × ℕ) : List ℤ :=
  (ts.drop p.1).take (p.2 - p.1)


def hlhr_intervalTurns (ts : List ℤ) (ps : List (ℕ × ℕ)) : List ℤ :=
  (ps.map (hlhr_intervalContent ts)).flatten


end StatMech.Universality
