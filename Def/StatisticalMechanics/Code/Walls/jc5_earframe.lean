/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc5_earCell (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]

end Walls
end StatMech
