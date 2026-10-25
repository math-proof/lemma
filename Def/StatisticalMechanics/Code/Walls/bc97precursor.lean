/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc96singlesiterewiring
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc97_boundaryGenuineFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc89_genuineTrifFinset ω n).filter (fun x => x ∉ box d (n - 1))


noncomputable def bc97_interiorGenuineFinset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc89_genuineTrifFinset ω n).filter (fun x => x ∈ box d (n - 1))


end StatMech.Walls
