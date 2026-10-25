/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


theorem bka_forceOpenFinset_empty (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
  funext e; simp [forceOpenFinset]


theorem bka_corridor_refl (G : Finset (Sym2 (Site d))) (a : Site d) :
    Relation.ReflTransGen (CorridorStep G) a a := Relation.ReflTransGen.refl


theorem bka_distinct_clusters (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : bcc_distinct_clusters_residue ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  refine ⟨a₁, a₂, a₃, ∅, a₁, a₂, a₃, hne, hadj,
    ⟨bka_corridor_refl ∅ a₁, bka_corridor_refl ∅ a₂, bka_corridor_refl ∅ a₃⟩, ?_, ?_⟩
  · 
    rw [bka_forceOpenFinset_empty]
    exact ⟨hi1, hi2, hi3⟩
  · rw [bka_forceOpenFinset_empty]
    exact ⟨hd12, hd13, hd23⟩


theorem bka_disjointRouting_of_mergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : DisjointCorridorRouting ω :=
  bcc_disjointRouting_of_residue ω (bka_distinct_clusters ω h)


theorem bka_routing_of_mergeFree (n : ℕ)
    (hmf : ∀ ω ∈ threeMeetBox d n, bka_MergeFree ω) :
    hrHD_DisjointRouting d n := by
  classical
  intro ω hω
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := hmf ω hω
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  refine ⟨F, a₁, a₂, a₃, ?_⟩
  
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> (rw [h]; exact Sym2.mem_mk_left _ _)
  have hrm : removeSite (0:Site d) (forceOpenFinset F ω) = removeSite (0:Site d) ω :=
    removeSite_forceOpen_eq 0 F hFmem ω
  
  refine ⟨hne, hadj, ?_, ?_, ?_, ?_⟩
  · rw [hrm]; exact ⟨hi1, hi2, hi3⟩
  · rw [hrm]; intro hc; exact hd12 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd13 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd23 (cluster_eq_of_connected hc)


theorem bka_rhoOpenEdge_decompose (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {u v : Site d}
    (hadj : (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v) :
    (hypercubicLattice d).Adj u v ∧ (0 : Site d) ∉ s(u, v) ∧
      (IsOpenEdge d ω u v ∨ s(u, v) ∈ G) := by
  rw [openSubgraph_adj] at hadj
  obtain ⟨hlat, hval⟩ := hadj
  have h0 : (0 : Site d) ∉ s(u, v) := by
    intro hmem; rw [removeSite_apply_of_mem hmem] at hval; exact absurd hval (by simp)
  rw [removeSite_apply_of_notMem h0] at hval
  refine ⟨hlat, h0, ?_⟩
  by_cases hg : s(u, v) ∈ G
  · exact Or.inr hg
  · rw [forceOpenFinset_of_notMem hg] at hval; exact Or.inl ⟨hlat, hval⟩


theorem bka_no_crossing_edge (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hne : cluster d ω x ≠ cluster d ω y) {u v : Site d}
    (hu : u ∈ cluster d ω x) (hv : v ∈ cluster d ω y) (hedge : IsOpenEdge d ω u v) :
    False := by
  rw [mem_cluster] at hu hv
  exact hne (cluster_eq_of_connected (hu.trans (hedge.connected.trans hv.symm)))


theorem bka_region_rhoAdjClosed (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) (R : Set (Site d))
    (homega : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
    (hG : ∀ u v, u ∈ R → s(u, v) ∈ G → v ∈ R) :
    ∀ u v, u ∈ R →
      (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ R := by
  intro u v hu hadj
  obtain ⟨_, _, hcase⟩ := bka_rhoOpenEdge_decompose ω G hadj
  rcases hcase with hopen | hg
  · exact homega u v hu hopen
  · exact hG u v hu hg


end Percolation
end StatMech
