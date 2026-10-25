/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


theorem bka_disjointRouting_of_corridorConfinement (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_CorridorConfinement ω) : DisjointCorridorRouting ω := h


theorem bka_distinct_clusters_of_corridorConfinement (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_CorridorConfinement ω) : bcc_distinct_clusters_residue ω := by
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, S₁, S₂, S₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite 0 (forceOpenFinset G ω) with hϱ
  
  
  have hdist : cluster d ϱ a₁ ≠ cluster d ϱ a₂ ∧ cluster d ϱ a₁ ≠ cluster d ϱ a₃ ∧
      cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
    (bcc_disjoint_sides_iff_clusters_distinct ϱ a₁ a₂ a₃).mp
      ⟨S₁, S₂, S₃, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩
  exact ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, hne, hadj, ⟨hc1, hc2, hc3⟩, ⟨hw1, hw2, hw3⟩, hdist⟩


theorem bka_residue_iff_corridorConfinement (ω : ConfigSpace (Sym2 (Site d))) :
    bcc_distinct_clusters_residue ω ↔ bka_CorridorConfinement ω := by
  constructor
  · intro h; exact bcc_disjointRouting_of_residue ω h
  · intro h; exact bka_distinct_clusters_of_corridorConfinement ω h

end Percolation
end StatMech
