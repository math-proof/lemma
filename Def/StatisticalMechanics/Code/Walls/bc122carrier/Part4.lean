/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part3
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


def bc122_starRel (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d) :
    Site d → Site d → Prop :=
  fun u v => ∃ y ∈ bc122_hubs ω L R, ∃ j : Fin 3,
    (u = y ∧ v = arm y j) ∨ (v = y ∧ u = arm y j)


noncomputable def bc122_starGraph (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (arm : Site d → Fin 3 → Site d) :
    SimpleGraph (↑(bc122_carrier ω L R arm) : Type) :=
  SimpleGraph.fromRel (fun u v => bc122_starRel ω L R arm (u : Site d) (v : Site d))


end StatMech.Walls
