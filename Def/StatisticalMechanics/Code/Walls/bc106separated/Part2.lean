/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc106separated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc105contraction
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc73sublattice.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc106separated
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc106_separatedTrifFinset (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) :
    Finset (Site d) := by
  classical
  exact (bc61_coarseTrifFinset ω L R).filter (fun y => bc73_onSublattice L y)


noncomputable def bc106_separatedTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : ℕ :=
  (bc106_separatedTrifFinset ω L R).card


end StatMech.Walls
