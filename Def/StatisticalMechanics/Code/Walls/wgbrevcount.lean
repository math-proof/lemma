module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wgbrevcount
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def wgb_WindsAtMostOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  |revCount K a| ≤ 1


def wgb_WindsAtLeastOnce (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  revCount K a ≠ 0


end Lattice
end StatMech
