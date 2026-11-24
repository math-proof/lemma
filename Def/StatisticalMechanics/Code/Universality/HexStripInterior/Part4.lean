module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripInterior.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexStrip_singleRightDReg (a : ℂ) (h0 : ℤ) : ℂ → ℤ → Prop :=
  fun m d => (m = a ∧ d = h0)
    ∨ (m = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1)) ∧ d = h0 + (-1))


end StatMech.Universality
