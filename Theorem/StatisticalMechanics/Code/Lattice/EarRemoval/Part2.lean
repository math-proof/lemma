/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Def.StatisticalMechanics.Code.Lattice.EarRemoval.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem turningIsFullRevolution_of_simplePolygon (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : SimplePolygonCornerBalance K a) :
    TurningIsFullRevolution K a :=
  turningIsFullRevolution_of_corner_diff_four K a h


theorem simplePolygonCornerBalance_iff (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    SimplePolygonCornerBalance K a ↔ TurningIsFullRevolution K a := by
  unfold SimplePolygonCornerBalance TurningIsFullRevolution
  rw [totalTurnZ_eq_cornerBalance]


theorem unitCell_simplePolygonCornerBalance :
    SimplePolygonCornerBalance unitCell ucBase :=
  (simplePolygonCornerBalance_iff unitCell ucBase).mpr unitCell_turningIsFullRevolution


end Lattice
end StatMech
