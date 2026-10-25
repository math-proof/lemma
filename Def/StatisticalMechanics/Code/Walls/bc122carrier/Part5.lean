/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part4
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


open Classical in


noncomputable def bc122_ιU (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) (base : ↑(bc122_carrier ω L R arm)) :
    Site d → ↑(bc122_carrier ω L R arm) :=
  fun z => if hz : z ∈ bc122_carrier ω L R arm then ⟨z, hz⟩ else base

end StatMech.Walls
