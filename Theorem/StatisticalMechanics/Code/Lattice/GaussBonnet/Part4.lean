/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Def.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem turningIsFullRevolution_of_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (h : EulerCharOne K a) :
    TurningIsFullRevolution K a := by
  apply turningIsFullRevolution_of_revCount
  have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
  rcases h with h | h
  · left; rw [h, hchi]; rfl
  · right; rw [h, hchi]; rfl


theorem eulerCharOne_iff_turningIsFullRevolution (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ TurningIsFullRevolution K a := by
  constructor
  · exact turningIsFullRevolution_of_eulerCharOne K a hp
  · intro h
    have hchi : contourEulerChar (dartOrbitPeriod K a) = 1 := contourEulerChar_eq_one hp
    unfold EulerCharOne
    rw [hchi]
    rcases (turningIsFullRevolution_iff_revCount K a).mp h with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]; rfl


theorem unitCell_eulerCharOne : EulerCharOne unitCell ucBase := by
  have hp : 3 ≤ dartOrbitPeriod unitCell ucBase := by
    rw [unitCell_orbitPeriod_eq_four]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution unitCell ucBase hp).mpr
    unitCell_turningIsFullRevolution


theorem domino_eulerCharOne : EulerCharOne domino dmBase := by
  have hp : 3 ≤ dartOrbitPeriod domino dmBase := by
    rw [domino_orbitPeriod_eq_six]; norm_num
  exact (eulerCharOne_iff_turningIsFullRevolution domino dmBase hp).mpr
    domino_turningIsFullRevolution

end Lattice
end StatMech
