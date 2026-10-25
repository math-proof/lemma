/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc4_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Walls.jc5_firstreturn
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_earframe.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc5_NoReentry (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) : Prop :=
  ∀ i, i < dartOrbitPeriod K a → ¬ jc4_FootprintFree K a r i →
    ∀ k, k ≤ i → ¬ jc4_FootprintFree K a r k


def jc5_TouchingConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
    ¬ jc4_FootprintFree K a r j


end Walls
end StatMech
