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
import Theorem.StatisticalMechanics.Code.Walls.wtctouchingconvex.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def wtc_TouchingDartsConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → k < dartOrbitPeriod K a →
    jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) →
    jc5_ProbesEarFootprint r ((dartNext K)^[k] a.1) →
    jc5_ProbesEarFootprint r ((dartNext K)^[j] a.1)


end Walls
end StatMech
