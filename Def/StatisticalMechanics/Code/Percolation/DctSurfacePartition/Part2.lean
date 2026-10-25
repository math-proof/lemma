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
import Theorem.StatisticalMechanics.Code.Percolation.DctSurfacePartition
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


def connBdry (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ (hx : x ∈ box d n) (y : Site d) (hy : y ∈ box d n),
    y ∈ vertexBoundary d n ∧ ConnectedWithin d ω (box d n) ⟨x, hx⟩ ⟨y, hy⟩


noncomputable def surfaceSet (d n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) : Finset (Site d) := by
  classical
  exact (boxFinset d n).filter (fun x => ¬ connBdry d n ω x)

end Percolation
end StatMech
