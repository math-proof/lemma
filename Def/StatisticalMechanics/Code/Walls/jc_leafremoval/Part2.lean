/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_leafremoval.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval
open SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def jc_domino : Set (Site 2) := {![0, 0], ![1, 0]}

end Walls
end StatMech
