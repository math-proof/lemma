module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part2


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


noncomputable def hexInfra_stepReSum (h : ℤ) : List ℤ → ℝ
  | [] => 0
  | t :: ts =>
      (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re + hexInfra_stepReSum (h + t) ts

end StatMech.Universality
