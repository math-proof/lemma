module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Walls.jc10farupeven
public import Theorem.StatisticalMechanics.Code.Walls.jc10localconstancy
public import Theorem.StatisticalMechanics.Code.Walls.jc10cornerexists
public import Theorem.StatisticalMechanics.Code.Walls.jc10cornercellinK
public import Def.StatisticalMechanics.Code.Walls.jc10core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem jc10core_topWallEdge_mk (c x y : Site 2) :
    jc10core_topWallEdge c s(x, y) ↔
      (x 1 = y 1 ∧ x 1 = c 1) ∧
      ((x 0 = c 0 - 1 ∧ y 0 = c 0) ∨ (y 0 = c 0 - 1 ∧ x 0 = c 0)) := by
  unfold jc10core_topWallEdge; rfl

end Walls
end StatMech
