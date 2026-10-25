/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc13core
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc14_rayPt_mem_cluster_of_runsAlong (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    hrHD_rayPt j 1 ∈ cluster d ω x := by
  obtain ⟨_, _, hxe1, _, _⟩ := h
  exact hxe1


theorem bc14_axes_distinct (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d} {j k : Fin d}
    (hne : cluster d ω x ≠ cluster d ω y)
    (hx : crr_ClusterRunsAlongAxis ω x j) (hy : crr_ClusterRunsAlongAxis ω y k) :
    j ≠ k := by
  intro hjk
  subst hjk
  have hxmem : hrHD_rayPt j 1 ∈ cluster d ω x := bc14_rayPt_mem_cluster_of_runsAlong ω x j hx
  have hymem : hrHD_rayPt j 1 ∈ cluster d ω y := bc14_rayPt_mem_cluster_of_runsAlong ω y j hy
  have hdisj : Disjoint (cluster d ω x) (cluster d ω y) := bmm_regions_disjoint ω hne
  have hmem : hrHD_rayPt j 1 ∈ cluster d ω x ∩ cluster d ω y := ⟨hxmem, hymem⟩
  rw [Set.disjoint_iff_inter_eq_empty.mp hdisj] at hmem
  exact absurd hmem (Set.notMem_empty _)


end Walls
end StatMech
