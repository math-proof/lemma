/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_singlecycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Def.StatisticalMechanics.Code.Walls.jc6_singlecycle
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc6_singleCycle (K : Set (Site 2)) (hK : K.Finite) : jc6_SingleCycle K := by
  intro a
  exact ⟨jc6_orbit_injOn_Iio K a,
    fun hj hk => jc6_iterate_eq_iff K a hj hk,
    fun hj hk hjd hkd => jc6_no_dart_recurs K a hj hk hjd hkd,
    jc6_orbit_darts_nodup K a,
    jc6_dartOrbitWalk_isCycle K hK a⟩


end Walls
end StatMech
