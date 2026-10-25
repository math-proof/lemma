/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Percolation.InfiniteClusterTail.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

theorem disjoint_clusters_of_ne (omega : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hne : cluster d omega x ≠ cluster d omega y) :
    Disjoint (cluster d omega x) (cluster d omega y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact hne ((cluster_eq_of_connected hzx).trans (cluster_eq_of_connected hzy).symm)


theorem threeInfiniteClusters_have_disjoint_tails
    (omega : ConfigSpace (Sym2 (Site d))) (K : Finset (Site d))
    (x1 x2 x3 : Site d)
    (hx1 : x1 ∈ K) (hx2 : x2 ∈ K) (hx3 : x3 ∈ K)
    (hi1 : (cluster d omega x1).Infinite)
    (hi2 : (cluster d omega x2).Infinite)
    (hi3 : (cluster d omega x3).Infinite)
    (hne12 : cluster d omega x1 ≠ cluster d omega x2)
    (hne13 : cluster d omega x1 ≠ cluster d omega x3)
    (hne23 : cluster d omega x2 ≠ cluster d omega x3) :
    ∃ D1 : InfiniteClusterTailData omega K x1,
      ∃ D2 : InfiniteClusterTailData omega K x2,
        ∃ D3 : InfiniteClusterTailData omega K x3,
          Disjoint D1.tail D2.tail ∧ Disjoint D1.tail D3.tail ∧
            Disjoint D2.tail D3.tail := by
  let D1 := infiniteClusterTailData omega x1 hi1 K hx1
  let D2 := infiniteClusterTailData omega x2 hi2 K hx2
  let D3 := infiniteClusterTailData omega x3 hi3 K hx3
  have hc12 := disjoint_clusters_of_ne omega hne12
  have hc13 := disjoint_clusters_of_ne omega hne13
  have hc23 := disjoint_clusters_of_ne omega hne23
  exact ⟨D1, D2, D3,
    hc12.mono D1.tail_subset_cluster D2.tail_subset_cluster,
    hc13.mono D1.tail_subset_cluster D3.tail_subset_cluster,
    hc23.mono D2.tail_subset_cluster D3.tail_subset_cluster⟩

end StatMech.Percolation
