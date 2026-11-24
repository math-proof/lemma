module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc_steplocal
public import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part2
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc3_farDart : Dart :=
  mkDart (![10, 0] : Site 2) (![1, 0] : Site 2) (by
    unfold unitWt
    rw [Fin.sum_univ_two]
    simp)

end Walls
end StatMech
