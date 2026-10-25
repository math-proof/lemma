/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tex_insertion_of_attachData (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    tre_MergeFreeInsertion ω := by
  obtain ⟨hcd12, hcd13, hcd23⟩ := hd
  obtain ⟨a₁, a₂, a₃, W, hadj, hW, ⟨ha1, ha2, ha3⟩, ⟨hg1, hg2, hg3⟩,
    ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩⟩ := h
  
  have hdj12 : Disjoint (cluster d ω x₁) (cluster d ω x₂) := bmm_regions_disjoint ω hcd12
  have hdj13 : Disjoint (cluster d ω x₁) (cluster d ω x₃) := bmm_regions_disjoint ω hcd13
  have hdj23 : Disjoint (cluster d ω x₂) (cluster d ω x₃) := bmm_regions_disjoint ω hcd23
  
  have hne12 : a₁ ≠ a₂ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha2 hdj12
  have hne13 : a₁ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha1 ha3 hdj13
  have hne23 : a₂ ≠ a₃ := bmm_distinct_neighbours_of_disjoint_regions ha2 ha3 hdj23
  exact ⟨a₁, a₂, a₃, W, x₁, x₂, x₃, cluster d ω x₁, cluster d ω x₂, cluster d ω x₃,
    ⟨hne12, hne13, hne23⟩, hadj, hW, ⟨hc1, hc2, hc3⟩, ⟨hri1, hri2, hri3⟩,
    ⟨ha1, ha2, ha3⟩,
    ⟨bmm_cluster_omegaClosed ω x₁, bmm_cluster_omegaClosed ω x₂, bmm_cluster_omegaClosed ω x₃⟩,
    ⟨hg1, hg2, hg3⟩, ⟨hdj12, hdj13, hdj23⟩⟩


theorem tex_threeClustersReachOrigin (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tre_threeClustersReachOrigin_of_insertion ω (tex_insertion_of_attachData ω x₁ x₂ x₃ hd h)


theorem tex_mergeFree (ω : ConfigSpace (Sym2 (Site d))) (x₁ x₂ x₃ : Site d)
    (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃)
    (h : tex_AttachData ω x₁ x₂ x₃) :
    ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
  obtain ⟨W, hreach⟩ := tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd h
  exact ⟨W, mco_mergeFree (forceOpenFinset W ω) hreach⟩


end Percolation
end StatMech
