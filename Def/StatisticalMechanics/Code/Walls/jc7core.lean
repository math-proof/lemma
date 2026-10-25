/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7stepfacebridge
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc7core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc7_SinglePass (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
    ¬ jc4_FootprintFree K a r j


end Walls
end StatMech
