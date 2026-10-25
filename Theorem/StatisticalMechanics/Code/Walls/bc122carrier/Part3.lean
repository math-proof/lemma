/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Def.StatisticalMechanics.Code.Walls.bc122carrier.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc122_hub_mem_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {y : Site d} (hy : y ∈ bc122_hubs ω L R) :
    y ∈ bc122_carrier ω L R arm := by
  classical
  unfold bc122_carrier; exact Finset.mem_union_left _ hy

theorem bc122_tip_mem_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {y : Site d} (hy : y ∈ bc122_hubs ω L R) (j : Fin 3) :
    arm y j ∈ bc122_carrier ω L R arm := by
  classical
  unfold bc122_carrier
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨y, hy, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩


end StatMech.Walls
