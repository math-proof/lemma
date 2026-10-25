/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part3
import Def.StatisticalMechanics.Code.Percolation.AvoidingAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem ava_avoidingAttachment_of_removeSiteCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hx : x ≠ 0) (hadj : (hypercubicLattice d).Adj 0 a)
    (hmemR : a ∈ cluster d (removeSite 0 ω) x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  have hc : Connected d (removeSite 0 ω) a x := (mem_cluster.mp hmemR).symm
  have hmem : a ∈ cluster d ω x := by
    rw [mem_cluster]; exact ava_connected_of_removeSite ω (mem_cluster.mp hmemR)
  obtain ⟨w, hw⟩ := ava_avoiding_walk_of_removeSite ω hx hc
  exact ⟨a, w, hadj, hmem, hw, hri⟩


theorem ava_avoidingAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : cla_AvoidingAttachment ω x := by
  obtain ⟨hx, hri, a, hadj, hmemR⟩ := h
  exact ava_avoidingAttachment_of_removeSiteCluster ω hx hadj hmemR hri


theorem ava_clusterAttachment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : ava_AvoidingRoutingResidue ω x) : bma_ClusterAttachment ω x :=
  cla_clusterAttachment_of_avoidingAttachment ω x (ava_avoidingAttachment ω x h)


theorem ava_avoidingAttachment_of_notMemCluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (hadj : (hypercubicLattice d).Adj 0 a) (hmem : a ∈ cluster d ω x)
    (h0 : (0 : Site d) ∉ cluster d ω x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x := by
  obtain ⟨w⟩ := (mem_cluster.mp hmem).symm
  exact ⟨a, w, hadj, hmem, ava_origin_notMem_support_of_notMem_cluster ω w h0, hri⟩


theorem ava_avoidingRoutingResidue_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    ava_AvoidingRoutingResidue ω x :=
  ⟨hadj.ne.symm, hri, x, hadj, self_mem_cluster (removeSite 0 ω) x⟩


theorem ava_avoidingAttachment_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hri : (cluster d (removeSite 0 ω) x).Infinite) :
    cla_AvoidingAttachment ω x :=
  ava_avoidingAttachment ω x (ava_avoidingRoutingResidue_of_neighbour ω x hadj hri)


end Percolation
end StatMech
