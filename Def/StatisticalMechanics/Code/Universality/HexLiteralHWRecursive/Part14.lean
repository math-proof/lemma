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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part13


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


def hlhr_latticeHeight (ts : List ℤ) (k : ℕ) : ℤ :=
  let p := (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
    (ts.take k)).pos
  p.x - p.y


end StatMech.Universality
