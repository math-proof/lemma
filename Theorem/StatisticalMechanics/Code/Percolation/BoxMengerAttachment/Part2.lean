/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoxMengerAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Percolation.BoxMengerAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bma_attachment_of_three_clusterAttachments (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d)
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h1 : bma_ClusterAttachment ω x₁) (h2 : bma_ClusterAttachment ω x₂)
    (h3 : bma_ClusterAttachment ω x₃) :
    ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧
      ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧
        (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧
        (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧
      (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧
        Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧
      ((cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite) := by
  classical
  obtain ⟨a₁, W₁, hadj1, hW1, hin1, hmem1, hc1, hri1⟩ := h1
  obtain ⟨a₂, W₂, hadj2, hW2, hin2, hmem2, hc2, hri2⟩ := h2
  obtain ⟨a₃, W₃, hadj3, hW3, hin3, hmem3, hc3, hri3⟩ := h3
  
  have hd12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := bmm_regions_disjoint ω hcd12
  have hd13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := bmm_regions_disjoint ω hcd13
  have hd23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := bmm_regions_disjoint ω hcd23
  set W : Finset (Sym2 (Site d)) := W₁ ∪ W₂ ∪ W₃ with hWdef
  
  have hs1 : W₁ ⊆ W := by rw [hWdef]; exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hs2 : W₂ ⊆ W := by rw [hWdef]; exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hs3 : W₃ ⊆ W := by rw [hWdef]; exact Finset.subset_union_right
  refine ⟨a₁, a₂, a₃, W, ⟨hadj1, hadj2, hadj3⟩, ?_, ⟨hmem1, hmem2, hmem3⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨hri1, hri2, hri3⟩⟩
  · 
    rw [hWdef]; exact bma_originAvoiding_union hW1 hW2 hW3
  · 
    rw [hWdef]; exact bma_internal_union hin1 hin2 hin3 hd12 hd13
  · 
    rw [hWdef]
    intro u v hu hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with (h | h) | h
    · exact bma_internal_of_edgesIn_disjoint hin1 hd12.symm u v hu h
    · exact bma_internal_of_edgesIn hin2 u v hu h
    · exact bma_internal_of_edgesIn_disjoint hin3 hd23 u v hu h
  · 
    rw [hWdef]
    intro u v hu hmem
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with (h | h) | h
    · exact bma_internal_of_edgesIn_disjoint hin1 hd13.symm u v hu h
    · exact bma_internal_of_edgesIn_disjoint hin2 hd23.symm u v hu h
    · exact bma_internal_of_edgesIn hin3 u v hu h
  · exact bma_connected_of_sub ω hs1 hc1
  · exact bma_connected_of_sub ω hs2 hc2
  · exact bma_connected_of_sub ω hs3 hc3


end Percolation
end StatMech
