module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
public import Theorem.StatisticalMechanics.Code.Walls.jc_steplocal
public import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc4_footprintagree
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_footprintdartsfinite.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc5_ProbesEarFootprint (r : Site 2) (e : Dart) : Prop :=
  jc_headTravel e ∈ jc3_earFootprint r ∨ jc_tailTravel e ∈ jc3_earFootprint r


end Walls
end StatMech
