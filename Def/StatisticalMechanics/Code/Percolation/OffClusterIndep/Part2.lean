/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part2
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


def offClusterBoxCrossing (d : ℕ) (C : Set (Site d)) (y : Site d) (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ z, z ∉ box d (n - 1) ∧ ∃ (hy : y ∈ box d n \ C) (hz : z ∈ box d n \ C),
    ConnectedWithin d ω (box d n \ C) ⟨y, hy⟩ ⟨z, hz⟩


end Percolation
end StatMech
