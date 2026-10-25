/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterAttachment.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem ava_support_mem_cluster (ω : ConfigSpace (Sym2 (Site d))) {a x z : Site d}
    (w : (openSubgraph d ω).Walk a x) (hz : z ∈ w.support) :
    z ∈ cluster d ω x := by
  have hza : Connected d ω a z := (w.takeUntil z hz).reachable
  rw [mem_cluster]
  exact (Connected.symm w.reachable).trans hza


theorem ava_origin_notMem_support_of_notMem_cluster (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x)
    (h0 : (0 : Site d) ∉ cluster d ω x) :
    (0 : Site d) ∉ w.support :=
  fun hmem => h0 (ava_support_mem_cluster ω w hmem)


theorem ava_removeSite_openSubgraph_le (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite 0 ω) ≤ openSubgraph d ω := by
  intro x y h
  obtain ⟨hadj, hval⟩ := h
  refine ⟨hadj, ?_⟩
  by_cases h0 : (0 : Site d) ∈ s(x, y)
  · rw [removeSite_apply_of_mem h0] at hval; exact absurd hval (by simp)
  · rwa [removeSite_apply_of_notMem h0] at hval


theorem ava_origin_no_adj_removeSite (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite 0 ω)).Adj (0 : Site d) y := by
  rintro ⟨hadj, hval⟩
  have h0 : (0 : Site d) ∈ s((0 : Site d), y) := Sym2.mem_mk_left _ _
  rw [removeSite_apply_of_mem h0] at hval
  exact absurd hval (by simp)


theorem ava_connected_origin_eq (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (h : Connected d (removeSite 0 ω) (0 : Site d) x) : x = 0 := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p => exact absurd hadj (ava_origin_no_adj_removeSite ω _)


theorem ava_origin_notMem_cluster_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hx : x ≠ 0) : (0 : Site d) ∉ cluster d (removeSite 0 ω) x := by
  rw [mem_cluster]
  intro h
  exact hx (ava_connected_origin_eq ω h.symm)


theorem ava_avoiding_walk_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hx : x ≠ 0) (hc : Connected d (removeSite 0 ω) a x) :
    ∃ w : (openSubgraph d ω).Walk a x, (0 : Site d) ∉ w.support := by
  obtain ⟨wr⟩ := hc
  refine ⟨wr.mapLe (ava_removeSite_openSubgraph_le ω), ?_⟩
  rw [SimpleGraph.Walk.support_mapLe_eq_support]
  intro hmem
  exact ava_origin_notMem_cluster_removeSite ω hx
    (ava_support_mem_cluster (removeSite 0 ω) wr hmem)


theorem ava_connected_of_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (hc : Connected d (removeSite 0 ω) a x) : Connected d ω a x :=
  hc.mono (ava_removeSite_openSubgraph_le ω)


end Percolation
end StatMech
