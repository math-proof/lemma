/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc111routing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc61coarsebox.Part5
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc111_measurableSet_coarsePrecursor (L : ℕ) (a₁ a₂ a₃ b₁ b₂ b₃ : Site d) :
    MeasurableSet (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃) := by
  classical
  set T : Finset (Site d) := bc61_boxAround d L 0 with hT
  
  set guard : Prop :=
    (b₁ ∈ T ∧ b₂ ∈ T ∧ b₃ ∈ T) ∧
    ((hypercubicLattice d).Adj b₁ a₁ ∧ (hypercubicLattice d).Adj b₂ a₂ ∧
      (hypercubicLattice d).Adj b₃ a₃) with hguard
  have heq : bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃
      = (if guard then Set.univ else ∅)
          ∩ ({ω | (cluster d (removeSites T ω) a₁).Infinite} ∩
              {ω | (cluster d (removeSites T ω) a₂).Infinite} ∩
              {ω | (cluster d (removeSites T ω) a₃).Infinite})
          ∩ ({ω | ¬ Connected d (removeSites T ω) a₁ a₂} ∩
              {ω | ¬ Connected d (removeSites T ω) a₁ a₃} ∩
              {ω | ¬ Connected d (removeSites T ω) a₂ a₃}) := by
    ext ω
    simp only [bc62_CoarseTrifPrecursor, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
      refine ⟨⟨?_, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs12, hs13⟩, hs23⟩⟩
      rw [if_pos ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩⟩]; exact Set.mem_univ _
    · rintro ⟨⟨hif, ⟨⟨hi1, hi2⟩, hi3⟩⟩, ⟨⟨hs12, hs13⟩, hs23⟩⟩
      by_cases hg : guard
      · obtain ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩⟩ := hg
        exact ⟨⟨hb1, hb2, hb3⟩, ⟨hadj1, hadj2, hadj3⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
      · rw [if_neg hg] at hif; exact absurd hif (Set.notMem_empty _)
  rw [heq]
  apply MeasurableSet.inter
  apply MeasurableSet.inter
  · by_cases hg : guard
    · rw [if_pos hg]; exact MeasurableSet.univ
    · rw [if_neg hg]; exact MeasurableSet.empty
  · exact ((bc62_measurableSet_clusterInfinite_removeSites T a₁).inter
      (bc62_measurableSet_clusterInfinite_removeSites T a₂)).inter
      (bc62_measurableSet_clusterInfinite_removeSites T a₃)
  · exact (((bc62_measurableSet_connected_removeSites T a₁ a₂).compl).inter
      ((bc62_measurableSet_connected_removeSites T a₁ a₃).compl)).inter
      ((bc62_measurableSet_connected_removeSites T a₂ a₃).compl)


end StatMech.Walls
