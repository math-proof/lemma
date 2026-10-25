/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem site2_eq (x y x' y' : ℤ) : (![x, y] : Site 2) = ![x', y'] ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl


theorem mem_cornerFaces_of_corner (a b : ℤ) (c : Site 2)
    (hc : c = ![a, b] ∨ c = ![a + 1, b] ∨ c = ![a + 1, b + 1] ∨ c = ![a, b + 1]) :
    (![a, b] : Site 2) ∈ cornerFaces c := by
  have mk : ∀ x y : ℤ, x = a → y = b → (![x, y] : Site 2) = ![a, b] := by
    rintro x y rfl rfl; rfl
  rcases hc with rfl | rfl | rfl | rfl
  · show (![a, b] : Site 2) ∈ cornerFaces ![a, b]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem; rw [Finset.mem_singleton]
  · show (![a, b] : Site 2) ∈ cornerFaces ![a + 1, b]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; rw [Finset.mem_insert]
    exact Or.inl (mk (a + 1 - 1) b (by omega) rfl).symm
  · show (![a, b] : Site 2) ∈ cornerFaces ![a + 1, b + 1]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.mem_insert]
    exact Or.inl (mk (a + 1 - 1) (b + 1 - 1) (by omega) (by omega)).symm
  · show (![a, b] : Site 2) ∈ cornerFaces ![a, b + 1]
    unfold cornerFaces
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
    rw [Finset.mem_insert]
    exact Or.inl (mk a (b + 1 - 1) rfl (by omega)).symm


theorem support_faceBoundaryGraph_subset (S : Set (Site 2)) :
    (faceBoundaryGraph S).support ⊆ ⋃ c ∈ S, (cornerFaces c : Set (Site 2)) := by
  intro f hf
  rw [SimpleGraph.mem_support] at hf
  obtain ⟨g, hadj⟩ := hf
  have hfeq : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hdeg : 0 < faceBoundaryDegree S (f 0) (f 1) := by
    rw [← degree_faceBoundaryGraph]
    rw [← hfeq]
    exact hadj.degree_pos_left
  have hcorner : (![f 0, f 1] : Site 2) ∈ S ∨ (![f 0 + 1, f 1] : Site 2) ∈ S
      ∨ (![f 0 + 1, f 1 + 1] : Site 2) ∈ S ∨ (![f 0, f 1 + 1] : Site 2) ∈ S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2, h3⟩ := hcon
    have e1 : bdInd S (faceCorner00 (f 0) (f 1)) (faceCorner10 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner00 faceCorner10; rw [if_neg]; tauto
    have e2 : bdInd S (faceCorner10 (f 0) (f 1)) (faceCorner11 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner10 faceCorner11; rw [if_neg]; tauto
    have e3 : bdInd S (faceCorner11 (f 0) (f 1)) (faceCorner01 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner11 faceCorner01; rw [if_neg]; tauto
    have e4 : bdInd S (faceCorner01 (f 0) (f 1)) (faceCorner00 (f 0) (f 1)) = 0 := by
      unfold bdInd faceCorner01 faceCorner00; rw [if_neg]; tauto
    unfold faceBoundaryDegree at hdeg
    rw [e1, e2, e3, e4] at hdeg
    omega
  rw [Set.mem_iUnion]
  rcases hcorner with h | h | h | h
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inl rfl)⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inl rfl))⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inr (Or.inl rfl)))⟩⟩
  · exact ⟨_, Set.mem_iUnion.mpr ⟨h, by
      rw [hfeq]; exact mem_cornerFaces_of_corner _ _ _ (Or.inr (Or.inr (Or.inr rfl)))⟩⟩


theorem exists_finset_support_faceBoundaryGraph (S : Set (Site 2)) (hS : S.Finite) :
    ∃ T : Finset (Site 2), (faceBoundaryGraph S).support ⊆ (T : Set (Site 2)) := by
  classical
  refine ⟨hS.toFinset.biUnion cornerFaces, ?_⟩
  intro f hf
  have hf' := support_faceBoundaryGraph_subset S hf
  rw [Set.mem_iUnion] at hf'
  obtain ⟨c, hc⟩ := hf'
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcS, hfc⟩ := hc
  rw [Finset.coe_biUnion]
  rw [Set.mem_iUnion]
  exact ⟨c, Set.mem_iUnion.mpr ⟨hS.mem_toFinset.mpr hcS, hfc⟩⟩


theorem exists_faceBoundaryGraph_adj_of_edgeBoundary (S : Set (Site 2)) {x y : Site 2}
    (h : (x, y) ∈ edgeBoundary 2 S) :
    ∃ f g : Site 2, (faceBoundaryGraph S).Adj f g := by
  obtain ⟨hadj, hsplit⟩ := h
  have hsplit_swap : (y ∈ S ↔ x ∉ S) := by
    classical
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> tauto
  have hnn : NearestNeighbour 2 x y := hadj
  rw [nearestNeighbour_iff_shift] at hnn
  obtain ⟨j, s, hs, hys⟩ := hnn
  set p := x 0 with hp
  set q := x 1 with hq
  have hx : x = ![p, q] := by funext i; fin_cases i <;> rfl
  fin_cases j
  · rcases hs with rfl | rfl
    · 
      have hy : y = ![p + 1, q] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> simp
      refine ⟨![p, q], ![p, q - 1], latAdj_bottom p q, ?_⟩
      rw [sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rw [bdEdge_mk, ← hx, ← hy]
      exact hsplit
    · 
      have hy : y = ![p - 1, q] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> (simp; try ring)
      refine ⟨![p - 1, q], ![p - 1, q - 1], latAdj_bottom (p - 1) q, ?_⟩
      rw [sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rw [bdEdge_mk]
      rw [show (p - 1) + 1 = p by ring]
      rw [← hx, ← hy]; exact hsplit_swap
  · rcases hs with rfl | rfl
    · 
      have hy : y = ![p, q + 1] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> simp
      refine ⟨![p, q], ![p - 1, q], latAdj_left p q, ?_⟩
      rw [sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rw [bdEdge_mk, ← hx, ← hy]
      exact hsplit
    · 
      have hy : y = ![p, q - 1] := by
        rw [hys, shift, hx]; funext i; fin_cases i <;> (simp; try ring)
      refine ⟨![p, q - 1], ![p - 1, q - 1], latAdj_left p (q - 1), ?_⟩
      rw [sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rw [bdEdge_mk]
      rw [show (q - 1) + 1 = q by ring]
      rw [← hx, ← hy]; exact hsplit_swap


theorem exists_dualCircuit_of_finite_of_edgeBoundary (S : Set (Site 2)) (hS : S.Finite)
    {x y : Site 2} (hxy : (x, y) ∈ edgeBoundary 2 S) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph S).Walk u u), c.IsCycle := by
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph S hS
  obtain ⟨f, g, hfg⟩ := exists_faceBoundaryGraph_adj_of_edgeBoundary S hxy
  obtain ⟨u, c, hcyc, _⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph S) T hT (degree_faceBoundaryGraph_even S) hfg
  exact ⟨u, c, hcyc⟩


theorem exists_dualCircuit_of_finite_cluster {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) {z : Site 2}
    (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle := by
  
  obtain ⟨a, b, hab⟩ :=
    walk_mem_edgeBoundary (cluster 2 ω o) w (self_mem_cluster ω o) hz
  exact exists_dualCircuit_of_finite_of_edgeBoundary (cluster 2 ω o) hfin hab

end Lattice
end StatMech
