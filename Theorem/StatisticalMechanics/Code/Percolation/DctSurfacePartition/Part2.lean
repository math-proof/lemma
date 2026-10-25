/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part2
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem mem_surfaceSet {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {x : Site d} :
    x ∈ surfaceSet d n ω ↔ x ∈ box d n ∧ ¬ connBdry d n ω x := by
  classical
  rw [surfaceSet, Finset.mem_filter, mem_boxFinset]


theorem surfaceSet_subset_box (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    surfaceSet d n ω ⊆ boxFinset d n := by
  intro x hx
  rw [mem_boxFinset]; exact (mem_surfaceSet.mp hx).1


end Percolation
end StatMech
