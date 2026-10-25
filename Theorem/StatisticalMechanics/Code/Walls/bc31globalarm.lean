/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc29armdiv.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc31_removeSites_isolated {T : Finset (Site d)} {t : Site d} (htT : t ∈ T)
    (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSites T ω)).Adj t y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSites] at hopen
  rw [if_pos ⟨t, htT, by simp⟩] at hopen
  exact Bool.false_ne_true hopen


theorem bc31_walk_avoids_removeSites {T : Finset (Site d)} {a b : Site d}
    {ω : ConfigSpace (Sym2 (Site d))} (haT : a ∉ T)
    (w : (openSubgraph d (removeSites T ω)).Walk a b) :
    ∀ z ∈ w.support, z ∉ T := by
  induction w with
  | nil =>
    intro z hz
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz; exact haT
  | @cons u v c huv w' ih =>
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact haT
    · 
      have hvT : v ∉ T := fun hv => bc31_removeSites_isolated hv ω u huv.symm
      exact ih hvT z hz


theorem bc31_edge_transfer {T : Finset (Site d)} {x : Site d}
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (huT : u ∉ T) (hvT : v ∉ T)
    (h : (openSubgraph d (removeSite x ω)).Adj u v) :
    (openSubgraph d (removeSites T ω)).Adj u v := by
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨hadj, hopen⟩ := h
  rw [removeSite] at hopen
  by_cases hx : x ∈ (s(u,v) : Sym2 (Site d))
  · rw [if_pos hx] at hopen; exact absurd hopen (by simp)
  · rw [if_neg hx] at hopen
    rw [removeSites]
    have hnoT : ¬ ∃ t ∈ T, t ∈ (s(u,v) : Sym2 (Site d)) := by
      rintro ⟨t, htT, htmem⟩
      rw [Sym2.mem_iff] at htmem
      rcases htmem with rfl | rfl
      · exact huT htT
      · exact hvT htT
    rw [if_neg hnoT]; exact hopen


theorem bc31_walk_transfer {T : Finset (Site d)} {x a b : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (w : (openSubgraph d (removeSite x ω)).Walk a b)
    (havoid : ∀ z ∈ w.support, z ∉ T) :
    Connected d (removeSites T ω) a b := by
  refine ⟨w.transfer (openSubgraph d (removeSites T ω)) ?_⟩
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    have hu : u ∈ w.support := w.fst_mem_support_of_mem_edges he
    have hv : v ∈ w.support := w.snd_mem_support_of_mem_edges he
    have hadj : (openSubgraph d (removeSite x ω)).Adj u v := w.adj_of_mem_edges he
    exact bc31_edge_transfer ω (havoid u hu) (havoid v hv) hadj


theorem bc31_infinite_globalCut_reaches_boundary (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) {a : Site d}
    (haT : a ∉ T) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSites T ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSites T ω)).Walk a z, ∀ v ∈ w.support, v ∉ T := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSites T ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, hr⟩ :=
    tfc_walk_crossing (openSubgraph d (removeSites T ω)) (fun v => v ∈ box d n) w habox hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSites T ω)) hbc
  refine ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, ?_⟩
  obtain ⟨wab⟩ := hr
  exact ⟨wab, bc31_walk_avoids_removeSites haT wab⟩


theorem bc31_globalCut_infinite_of_escaping {T : Finset (Site d)} {x a : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (hesc : ∀ m : ℕ, ∃ y, y ∉ box d m ∧
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a y, ∀ z ∈ w.support, z ∉ T) :
    (cluster d (removeSites T ω) a).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  obtain ⟨y, hy, w, havoid⟩ := hesc m
  exact ⟨y, hy, bc31_walk_transfer ω w havoid⟩


theorem bc31_support_connected {x a b z : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (w : (openSubgraph d (removeSite x ω)).Walk a b) (hz : z ∈ w.support) :
    Connected d (removeSite x ω) a z := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_append] at hz
  obtain ⟨q, r, rfl⟩ := hz
  exact ⟨q⟩


theorem bc31_globalCut_infinite_of_singleCut_Tfree {T : Finset (Site d)} {x a : Site d}
    (ω : ConfigSpace (Sym2 (Site d)))
    (hinf : (cluster d (removeSite x ω) a).Infinite)
    (hTfree : ∀ z, Connected d (removeSite x ω) a z → z ∉ T) :
    (cluster d (removeSites T ω) a).Infinite := by
  refine bc31_globalCut_infinite_of_escaping (x := x) ω (fun m => ?_)
  obtain ⟨y, hy, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf m
  obtain ⟨w⟩ := hyconn
  exact ⟨y, hy, w, fun z hz => hTfree z (bc31_support_connected ω w hz)⟩


end StatMech.Walls
