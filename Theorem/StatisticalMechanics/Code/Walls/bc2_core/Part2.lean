/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Def.StatisticalMechanics.Code.Walls.bc2_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc2_csc_of_forcedCorridorRouting (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc2_ForcedCorridorRouting ω) : csc_DistinctClusterCorridors ω := by
  obtain ⟨j₁, j₂, j₃, L₁, L₂, L₃, ⟨hj12, hj13, hj23⟩, ⟨hi1, hi2, hi3⟩, hsep12, hsep13, hsep23⟩ := h
  set G : Finset (Sym2 (Site d)) :=
    hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) ∪
      hrHD_corridorEdges j₃ (L₃ + 1) with hGdef
  
  have hs1 : hrHD_corridorEdges j₁ (L₁ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hs2 : hrHD_corridorEdges j₂ (L₂ + 1) ⊆ G := by
    rw [hGdef]; exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hs3 : hrHD_corridorEdges j₃ (L₃ + 1) ⊆ G := by rw [hGdef]; exact Finset.subset_union_right
  
  have hne12 : (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₂ 1 :=
    bc2_rayCell_distinct_of_ne hj12 one_ne_zero
  have hne13 : (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
    bc2_rayCell_distinct_of_ne hj13 one_ne_zero
  have hne23 : (hrHD_rayPt j₂ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
    bc2_rayCell_distinct_of_ne hj23 one_ne_zero
  refine ⟨hrHD_rayPt j₁ 1, hrHD_rayPt j₂ 1, hrHD_rayPt j₃ 1, G,
    hrHD_rayPt j₁ ((L₁ : ℤ) + 1), hrHD_rayPt j₂ ((L₂ : ℤ) + 1), hrHD_rayPt j₃ ((L₃ : ℤ) + 1),
    ⟨hne12, hne13, hne23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    ⟨bc2_corridorChain_in_union j₁ L₁ G hs1, bc2_corridorChain_in_union j₂ L₂ G hs2,
      bc2_corridorChain_in_union j₃ L₃ G hs3⟩,
    ⟨?_, ?_, ?_⟩, hsep12, hsep13, hsep23⟩
  · exact bc2_clusterInfinite_force_mono_origin ω G hi1
  · exact bc2_clusterInfinite_force_mono_origin ω G hi2
  · exact bc2_clusterInfinite_force_mono_origin ω G hi3


end Walls
end StatMech
