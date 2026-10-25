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
import Def.StatisticalMechanics.Code.Walls.fc_cellgeometry.Part2
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


theorem fc_cellBlockIso_nonvacuous (m n : ℕ) (hmn : m ≤ n) :
    ∃ c : Fin d → Fin (fc_Tcg m n),
      Nonempty (boxGraph d m ≃g qp_blkG (boxGraph d n) (fc_vanHoveTag m n) (some c)) := by
  have hT : 1 ≤ fc_Tcg m n := by
    change 1 ≤ ecz_T m n
    rw [ecz_T, Nat.le_div_iff_mul_le (by omega)]
    omega
  refine ⟨fun _ => ⟨0, by omega⟩, ⟨fc_cellBlockIso m n _⟩⟩

end VanHove
end StatMech.Walls
