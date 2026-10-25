/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wtctouchingconvex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Theorem.StatisticalMechanics.Code.Walls.wtctouchingconvex
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def wtc_touchingSteps (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    Set ℕ :=
  {i | i < dartOrbitPeriod K a ∧ ¬ jc4_FootprintFree K a r i}


end Walls
end StatMech
