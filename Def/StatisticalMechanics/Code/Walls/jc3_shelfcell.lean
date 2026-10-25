/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


def jc3_runRightEnd (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]


def jc3_downCell (c : Site 2) (len : ℤ) : Site 2 := jc3_runRightEnd c len + ![0, -1]

end Walls
end StatMech
