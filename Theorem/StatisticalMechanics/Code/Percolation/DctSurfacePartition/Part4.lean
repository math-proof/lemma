/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctSurfacePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part4
open MeasureTheory Function Set SimpleGraph
open scoped NNReal ENNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem disjoint_boxEdgesOutside (n : ℕ) (S : Finset (Site d)) :
    Disjoint (edgesWithinFinset S) (boxEdgesOutside d n S) := by
  rw [boxEdgesOutside]; exact disjoint_sdiff_self_right


theorem pair_mem_boxEdgesOutside {n : ℕ} {S : Finset (Site d)} {a z : Site d}
    (ha : a ∈ box d n) (hz : z ∈ box d n) (hor : a ∉ S ∨ z ∉ S) :
    s(a, z) ∈ boxEdgesOutside d n S := by
  classical
  rw [boxEdgesOutside, Finset.mem_sdiff]
  refine ⟨mem_boxEdgeFinset.mpr ⟨a, z, ha, hz, rfl⟩, ?_⟩
  rw [mem_edgesWithinFinset]
  rintro ⟨x, hx, y, hy, hxy⟩
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (rcases hor with h | h) <;> first | exact h hx | exact h hy


theorem walk_vertex_connBdry {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {a y : ↥(box d n)} (hy : (y : Site d) ∈ vertexBoundary d n)
    (w : (openSubgraphInduce d ω (box d n)).Walk a y)
    (v : ↥(box d n)) (hv : v ∈ w.support) :
    connBdry d n ω (v : Site d) :=
  ⟨v.2, y, y.2, hy, (w.dropUntil v hv).reachable⟩


theorem walk_transfer_avoidS {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Finset (Site d)}
    (hagree : ∀ x z : Site d, x ∈ box d n → z ∈ box d n →
       (x ∉ S ∨ z ∉ S) → ω s(x, z) = ω' s(x, z))
    {a b : ↥(box d n)} (w : (openSubgraphInduce d ω (box d n)).Walk a b)
    (hsupp : ∀ v ∈ w.support, (v : Site d) ∉ S) :
    Nonempty ((openSubgraphInduce d ω' (box d n)).Walk a b) := by
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons u v t hadj p ih =>
    have huS : (u : Site d) ∉ S := hsupp u (by simp)
    have hsupp' : ∀ z ∈ p.support, (z : Site d) ∉ S := fun z hz =>
      hsupp z (by simp only [Walk.support_cons, List.mem_cons]; right; exact hz)
    have heq : ω s((u : Site d), (v : Site d)) = ω' s((u : Site d), (v : Site d)) :=
      hagree u v u.2 v.2 (Or.inl huS)
    have hadj' : (openSubgraphInduce d ω' (box d n)).Adj u v := by
      simp only [openSubgraphInduce_adj, openSubgraph_adj]
      exact ⟨hadj.1, by rw [← heq]; exact hadj.2⟩
    obtain ⟨w'⟩ := ih hsupp'
    exact ⟨Walk.cons hadj' w'⟩


theorem connBdry_of_mem_boundary {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {y : Site d}
    (hy : y ∈ box d n) (hyb : y ∈ vertexBoundary d n) : connBdry d n ω y :=
  ⟨hy, y, hy, hyb, connectedWithin_refl ω (box d n) ⟨y, hy⟩⟩


theorem connBdry_of_open_edge {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} {u w : Site d}
    (hu : u ∈ box d n) (hw : w ∈ box d n) (hopen : IsOpenEdge d ω u w)
    (hcbw : connBdry d n ω w) : connBdry d n ω u := by
  obtain ⟨_, y, hy, hyb, hreach⟩ := hcbw
  have hadj : (openSubgraphInduce d ω (box d n)).Adj ⟨u, hu⟩ ⟨w, hw⟩ := by
    simp only [openSubgraphInduce_adj, openSubgraph_adj]; exact hopen
  exact ⟨hu, y, hy, hyb, (SimpleGraph.Adj.reachable hadj).trans hreach⟩


theorem connBdry_transfer {n : ℕ} {ω ω' : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S)
    (hagree : ∀ a z : Site d, a ∈ box d n → z ∈ box d n →
       (a ∉ S ∨ z ∉ S) → ω s(a, z) = ω' s(a, z))
    {x : Site d} (hxbox : x ∈ box d n) :
    connBdry d n ω x ↔ connBdry d n ω' x := by
  classical
  constructor
  · 
    intro hcb
    obtain ⟨hx, y, hy, hyb, hreach⟩ := hcb
    obtain ⟨w⟩ := hreach
    have hsupp : ∀ v ∈ w.support, (v : Site d) ∉ surfaceSet d n ω := by
      intro v hv; rw [mem_surfaceSet]; rintro ⟨_, hnc⟩
      exact hnc (walk_vertex_connBdry hyb w v hv)
    have hsuppS : ∀ v ∈ w.support, (v : Site d) ∉ S := fun v hv => hS ▸ hsupp v hv
    obtain ⟨w'⟩ := walk_transfer_avoidS hagree w hsuppS
    exact ⟨hx, y, hy, hyb, ⟨w'⟩⟩
  · 
    intro hcb'
    by_cases hxS : x ∈ S
    · exfalso
      obtain ⟨hx, y, hy, hyb, hreach'⟩ := hcb'
      obtain ⟨w⟩ := hreach'
      have hyS : (⟨y, hy⟩ : ↥(box d n)) ∉ ({v : ↥(box d n) | (v : Site d) ∈ S}) := by
        simp only [Set.mem_setOf_eq]
        intro hyc
        exact (mem_surfaceSet.mp (hS ▸ hyc)).2 (connBdry_of_mem_boundary hy hyb)
      have hxSset : (⟨x, hx⟩ : ↥(box d n)) ∈ ({v : ↥(box d n) | (v : Site d) ∈ S}) := hxS
      obtain ⟨u, ww, huS, hwwS, hadj, _⟩ :=
        exists_lastExit w ({v : ↥(box d n) | (v : Site d) ∈ S}) hxSset hyS
      have hwwSset : (ww : Site d) ∉ S := hwwS
      have hopen' : IsOpenEdge d ω' (u : Site d) (ww : Site d) := by
        have := hadj
        simp only [openSubgraphInduce_adj, openSubgraph_adj] at this; exact this
      have heq : ω s((u : Site d), (ww : Site d)) = ω' s((u : Site d), (ww : Site d)) :=
        hagree u ww u.2 ww.2 (Or.inr hwwSset)
      have hopen : IsOpenEdge d ω (u : Site d) (ww : Site d) :=
        ⟨hopen'.1, by rw [heq]; exact hopen'.2⟩
      have hcbww : connBdry d n ω (ww : Site d) := by
        by_contra hnc
        exact hwwSset (hS ▸ (mem_surfaceSet.mpr ⟨ww.2, hnc⟩))
      exact (mem_surfaceSet.mp (hS ▸ (huS : (u : Site d) ∈ S))).2
        (connBdry_of_open_edge u.2 ww.2 hopen hcbww)
    · 
      by_contra hnc
      exact hxS (hS ▸ (mem_surfaceSet.mpr ⟨hxbox, hnc⟩))


theorem surfaceSet_congr_outside (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    {S : Finset (Site d)} (hS : surfaceSet d n ω = S)
    (h : ∀ e ∈ (boxEdgesOutside d n S : Set (Sym2 (Site d))), ω e = ω' e) :
    surfaceSet d n ω' = S := by
  classical
  have hagree : ∀ a z : Site d, a ∈ box d n → z ∈ box d n →
      (a ∉ S ∨ z ∉ S) → ω s(a, z) = ω' s(a, z) := by
    intro a z ha hz hor
    exact h s(a, z) (by rw [Finset.mem_coe]; exact pair_mem_boxEdgesOutside ha hz hor)
  rw [← hS]
  ext x
  rw [mem_surfaceSet, mem_surfaceSet]
  by_cases hxbox : x ∈ box d n
  · simp only [hxbox, true_and]
    rw [connBdry_transfer hS hagree hxbox]
  · simp only [hxbox, false_and]


theorem surfaceEvent_dependsOn_outside (n : ℕ) (S : Finset (Site d)) :
    DependsOn ((surfaceEvent d n S).indicator (fun _ => (1 : ℝ)))
      ((boxEdgesOutside d n S : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff : ω ∈ surfaceEvent d n S ↔ ω' ∈ surfaceEvent d n S := by
    constructor
    · intro hω; exact surfaceSet_congr_outside n hω h
    · intro hω'
      exact surfaceSet_congr_outside n hω' (fun e he => (h e he).symm)
  by_cases hω : ω ∈ surfaceEvent d n S
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]


theorem surface_withinConn_indep (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) (S : Finset (Site d))
    (o x : Site d) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (withinConnEvent d (S : Set (Site d)) o x ∩ surfaceEvent d n S)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (withinConnEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (surfaceEvent d n S) :=
  withinConn_indep p hp S o x (surfaceEvent d n S) (boxEdgesOutside d n S)
    (disjoint_boxEdgesOutside n S) (surfaceEvent_dependsOn_outside n S)

end Percolation
end StatMech
