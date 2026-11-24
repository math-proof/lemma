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
public import Theorem.StatisticalMechanics.Code.Walls.jc10core.Part2
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


open Classical in


noncomputable def jc10core_topWallCount (c : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) : ℕ :=
  w.edges.countP (fun e => decide (jc10core_topWallEdge c e))


end Walls
end StatMech
