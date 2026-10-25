/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tre_threeClustersReachOrigin_of_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertion ω) :
    ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, R₁, R₂, R₃, hne, hadj, hW,
    ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨ho1, ho2, ho3⟩, ⟨hg1, hg2, hg3⟩, hd12, hd13, hd23⟩ := h
  refine ⟨W, a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ?_, ?_⟩
  · 
    exact ⟨tre_cluster_infinite_of_omega ω W hW x₁ hi1,
      tre_cluster_infinite_of_omega ω W hW x₂ hi2,
      tre_cluster_infinite_of_omega ω W hW x₃ hi3⟩
  · 
    set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
    
    have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
    have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
    have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
    
    have nd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ :=
      tre_branch_distinct_of_regions ω W a₁ a₂ R₁ R₂ hm1 hm2 ho1 hg1 ho2 hg2 hd12
    have nd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ :=
      tre_branch_distinct_of_regions ω W a₁ a₃ R₁ R₃ hm1 hm3 ho1 hg1 ho3 hg3 hd13
    have nd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
      tre_branch_distinct_of_regions ω W a₂ a₃ R₂ R₃ hm2 hm3 ho2 hg2 ho3 hg3 hd23
    refine ⟨?_, ?_, ?_⟩
    · rw [← ea1, ← ea2]; exact nd12
    · rw [← ea1, ← ea3]; exact nd13
    · rw [← ea2, ← ea3]; exact nd23


theorem tre_mergeFree_of_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertion ω) :
    ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
  obtain ⟨W, hreach⟩ := tre_threeClustersReachOrigin_of_insertion ω h
  exact ⟨W, mco_mergeFree (forceOpenFinset W ω) hreach⟩


end Percolation
end StatMech
