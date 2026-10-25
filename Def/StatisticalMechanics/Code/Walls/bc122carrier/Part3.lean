/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part2
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


noncomputable def bc122_carrier (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) : Finset (Site d) := by
  classical
  exact (bc122_hubs ω L R) ∪
    (bc122_hubs ω L R).biUnion (fun y => (Finset.univ : Finset (Fin 3)).image (fun j => arm y j))

end StatMech.Walls
