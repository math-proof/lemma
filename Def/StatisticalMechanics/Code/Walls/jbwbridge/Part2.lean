/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Theorem.StatisticalMechanics.Code.Walls.jbwbridge
open SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


def jbw_singleton : Set (Site 2) := {origin 2}


end Walls
end StatMech
