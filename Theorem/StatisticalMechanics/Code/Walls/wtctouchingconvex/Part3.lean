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
import Def.StatisticalMechanics.Code.Walls.wtctouchingconvex.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem wtc_touchingConvex_windowed_of_dartsConvex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hconv : wtc_TouchingDartsConvex K a r) :
    ∀ i j k, i < j → j < k → k < dartOrbitPeriod K a →
      ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
      ¬ jc4_FootprintFree K a r j := by
  intro i j k hij hjk hk hi hkt
  rw [wtc_touching_iff_probes] at hi hkt ⊢
  exact hconv i j k hij hjk hk hi hkt


theorem wtc_touchingDartsConvex_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, ¬ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1)) :
    wtc_TouchingDartsConvex K a r := by
  intro i _ _ _ _ _ hi _
  exact absurd hi (hfoot i)


theorem wtc_touchingConvex_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_TouchingConvex K a r :=
  jc5_touchingConvex_of_disjoint K a r hfoot


end Walls
end StatMech
