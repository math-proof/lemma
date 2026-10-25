/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Walls.kc3_upleftfacecell.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


noncomputable def kc3_ul_witLeftDart : Dart := mkDart ![1, 1] ![-1, 0] (by decide)

end Walls
end StatMech
