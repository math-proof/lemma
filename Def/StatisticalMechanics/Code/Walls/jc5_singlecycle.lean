/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_singlecycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc4_dartnextperm.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc5_SingleCycle (K : Set (Site 2)) : Prop :=
  ∀ a : {e : Dart // IsBoundaryDart K e},
    Set.InjOn (fun k => (dartNextSub K)^[k] a) (Set.Iio (dartOrbitPeriod K a)) ∧
    (∀ {j k : ℕ}, j < dartOrbitPeriod K a → k < dartOrbitPeriod K a →
      ((dartNextSub K)^[j] a = (dartNextSub K)^[k] a ↔ j = k)) ∧
    ((List.range (dartOrbitPeriod K a)).map (fun k => (dartNextSub K)^[k] a)).Nodup ∧
    (dartOrbitWalk K a).IsCycle


end Walls
end StatMech
