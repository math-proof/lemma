/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8tworowbands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.jc8tworowbands
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc8_DescentStaysLow (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (i : ℕ) : Prop :=
  (olb_orbitLoop K hK e he).getVert i 1 ≤ r 1 - 2


def jc8_TouchingFaceBand (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ) : Prop :=
  ¬ jc4_FootprintFree K ⟨e, he⟩ r j →
    r 1 - 1 ≤ (olb_orbitLoop K hK e he).getVert j 1


end Walls
end StatMech
