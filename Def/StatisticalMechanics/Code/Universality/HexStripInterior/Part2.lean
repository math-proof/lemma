module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior


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


def hexStripStaysInDir (dregion : ℂ → ℤ → Prop) (a : ℂ) (h0 : ℤ) (ts : List ℤ) : Prop :=
  ∀ p ∈ hexStripDirMids a h0 ts, dregion p.1 p.2


end StatMech.Universality
