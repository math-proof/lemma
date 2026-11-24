module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
public import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


def hexStripWinding_runningHead (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℤ := h0 + (ts.take k).sum


end StatMech.Universality
