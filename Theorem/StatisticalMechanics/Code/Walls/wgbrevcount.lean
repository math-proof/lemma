/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wgb_revCount_iff_eulerCharOne (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (hp : 3 ≤ dartOrbitPeriod K a) :
    EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
  rw [eulerCharOne_iff_turningIsFullRevolution K a hp, turningIsFullRevolution_iff_revCount]


end Lattice
end StatMech
