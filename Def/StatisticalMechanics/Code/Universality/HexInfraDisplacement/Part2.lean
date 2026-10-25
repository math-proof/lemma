/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


def hexInfra_headAccum (h : ℤ) : List ℤ → ℤ
  | [] => h
  | t :: ts => hexInfra_headAccum (h + t) ts

end StatMech.Universality
