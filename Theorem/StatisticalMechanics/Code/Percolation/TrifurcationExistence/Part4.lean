/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tre_threeClustersReachOrigin_of_insertionRho (ω : ConfigSpace (Sym2 (Site d)))
    (h : tre_MergeFreeInsertionRho ω) :
    ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  obtain ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, R₁, R₂, R₃, hne, hadj, hW,
    ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩, ⟨hm1, hm2, hm3⟩,
    ⟨hcl1, hcl2, hcl3⟩, hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
  refine ⟨W, a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ?_, ?_⟩
  · exact ⟨tre_cluster_infinite_of_omega ω W hW x₁ hi1,
      tre_cluster_infinite_of_omega ω W hW x₂ hi2,
      tre_cluster_infinite_of_omega ω W hW x₃ hi3⟩
  · have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
    have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
    have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
    have hs1 : cluster d ϱ a₁ ⊆ R₁ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₁ a₁ hm1 hcl1
    have hs2 : cluster d ϱ a₂ ⊆ R₂ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₂ a₂ hm2 hcl2
    have hs3 : cluster d ϱ a₃ ⊆ R₃ := DisjointPaths.cluster_subset_of_adjClosed ϱ R₃ a₃ hm3 hcl3
    have nd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₁ a₂ R₁ R₂ hs1 hs2 hd12
    have nd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₁ a₃ R₁ R₃ hs1 hs3 hd13
    have nd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ :=
      DisjointPaths.cluster_ne_of_disjoint ϱ a₂ a₃ R₂ R₃ hs2 hs3 hd23
    exact ⟨by rw [← ea1, ← ea2]; exact nd12, by rw [← ea1, ← ea3]; exact nd13,
      by rw [← ea2, ← ea3]; exact nd23⟩


theorem tre_mergeFreeInsertionRho_of_reachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : tre_MergeFreeInsertionRho ω := by
  classical
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, ⟨hc1, hc2, hc3⟩, ⟨hi1, hi2, hi3⟩,
    hd12, hd13, hd23⟩ := h
  set ϱ := removeSite (0 : Site d) ω with hϱ
  have hemp : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := bka_forceOpenFinset_empty ω
  
  have hrm : removeSite (0 : Site d) (forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω) = ϱ := by
    rw [hemp]
  
  have ea1 : cluster d ϱ a₁ = cluster d ϱ x₁ := cluster_eq_of_connected hc1
  have ea2 : cluster d ϱ a₂ = cluster d ϱ x₂ := cluster_eq_of_connected hc2
  have ea3 : cluster d ϱ a₃ = cluster d ϱ x₃ := cluster_eq_of_connected hc3
  have nda12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂ := by rw [ea1, ea2]; exact hd12
  have nda13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃ := by rw [ea1, ea3]; exact hd13
  have nda23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃ := by rw [ea2, ea3]; exact hd23
  have hne12 : a₁ ≠ a₂ := fun he => nda12 (by rw [he])
  have hne13 : a₁ ≠ a₃ := fun he => nda13 (by rw [he])
  have hne23 : a₂ ≠ a₃ := fun he => nda23 (by rw [he])
  
  have hdisj : ∀ (b c : Site d), cluster d ϱ b ≠ cluster d ϱ c →
      Disjoint (cluster d ϱ b) (cluster d ϱ c) := by
    intro b c hbc
    rw [Set.disjoint_iff]
    rintro z ⟨hzb, hzc⟩
    rw [mem_cluster] at hzb hzc
    exact hbc ((cluster_eq_of_connected hzb).trans (cluster_eq_of_connected hzc).symm)
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃,
    cluster d ϱ a₁, cluster d ϱ a₂, cluster d ϱ a₃,
    ⟨hne12, hne13, hne23⟩, hadj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro e he; exact absurd he (Finset.notMem_empty e)
  · 
    rw [hrm]; exact ⟨connected_rfl, connected_rfl, connected_rfl⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · show (cluster d (removeSite 0 ω) a₁).Infinite
      rw [← hϱ, ea1]; exact hi1
    · show (cluster d (removeSite 0 ω) a₂).Infinite
      rw [← hϱ, ea2]; exact hi2
    · show (cluster d (removeSite 0 ω) a₃).Infinite
      rw [← hϱ, ea3]; exact hi3
  · 
    exact ⟨self_mem_cluster ϱ a₁, self_mem_cluster ϱ a₂, self_mem_cluster ϱ a₃⟩
  · 
    rw [hrm]
    exact ⟨bcc_cluster_adjClosed ϱ a₁, bcc_cluster_adjClosed ϱ a₂,
      bcc_cluster_adjClosed ϱ a₃⟩
  · 
    exact ⟨hdisj a₁ a₂ nda12, hdisj a₁ a₃ nda13, hdisj a₂ a₃ nda23⟩

end Percolation
end StatMech
