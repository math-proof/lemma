/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc61coarsebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Def.StatisticalMechanics.Code.Walls.bc61coarsebox.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc61_mem_coarseTrifFinset {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d} :
    y ∈ bc61_coarseTrifFinset ω L R ↔
      y ∈ box d R ∧ bc61_IsCoarseTrifurcation ω L y := by
  classical
  rw [bc61_coarseTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset]


end StatMech.Walls
