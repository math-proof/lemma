module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List

open scoped BigOperators Real


def hexInfra_headAccum (h : ℤ) : List ℤ → ℤ
  | [] => h
  | t :: ts => hexInfra_headAccum (h + t) ts

end StatMech.Universality
