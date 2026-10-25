/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
open Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


def pww_a : Site 2 := ![0, 0]

def pww_b : Site 2 := ![1, 0]


end Walls
end StatMech
