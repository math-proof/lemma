/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Percolation.CorridorConfinement
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


theorem bcc_disjointRouting_of_residue (ω : ConfigSpace (Sym2 (Site d)))
    (h : bcc_distinct_clusters_residue ω) : DisjointCorridorRouting ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩,
    hd12, hd13, hd23⟩ := h
  exact bcc_disjointRouting_of_corridors_and_distinct ω a₁ a₂ a₃ G w₁ w₂ w₃
    hne hadj hc1 hc2 hc3 hw1 hw2 hw3 hd12 hd13 hd23

end Percolation
end StatMech
