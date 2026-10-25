/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgtgenuineforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
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


theorem bgt_mem_genuineTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (y : Site d) :
    y ∈ btr_genuineTrifFinset ω L R ↔ y ∈ box d R ∧ btr_IsGenuineCoarseTrif ω L y := by
  classical
  rw [btr_genuineTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]


end StatMech.Walls
