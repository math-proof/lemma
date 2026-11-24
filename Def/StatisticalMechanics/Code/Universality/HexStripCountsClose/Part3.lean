module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
public import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
public import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hsc_negEquiv : List ℤ ≃ List ℤ where
  toFun := hsc_negTurns
  invFun := hsc_negTurns
  left_inv := hsc_negTurns_negTurns
  right_inv := hsc_negTurns_negTurns


end StatMech.Universality
