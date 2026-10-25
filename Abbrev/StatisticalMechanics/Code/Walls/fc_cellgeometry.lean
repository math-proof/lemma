/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fc_cellgeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.Walls.fc_cellgeometry
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice


section VanHove

variable {d : ℕ}


abbrev fc_Tcg (m n : ℕ) : ℕ := ecz_T m n


abbrev fc_center (m n : ℕ) (c : Fin d → Fin (fc_Tcg m n)) : Site d := ecz_center m n c


noncomputable abbrev fc_vanHoveTag (m n : ℕ) (x : boxVerts d n) :
    Option (Fin d → Fin (fc_Tcg m n)) := ecz_vanHoveTag m n x


end VanHove
end StatMech.Walls
