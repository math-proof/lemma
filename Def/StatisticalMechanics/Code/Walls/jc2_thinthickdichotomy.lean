/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thinthickdichotomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_core
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def jc2_rightEnd (c : Site 2) (len : ℤ) : Site 2 := c + ![len, 0]


end Walls
end StatMech
