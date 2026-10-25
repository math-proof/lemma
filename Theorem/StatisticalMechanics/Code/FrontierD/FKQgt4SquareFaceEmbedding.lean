/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OuterLeafDual.Part7
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

theorem site_mem_box_of_int_bounds {m : Nat} {a b : Int}
    (ha : -(m : Int) ≤ a ∧ a ≤ m) (hb : -(m : Int) ≤ b ∧ b ≤ m) :
    (![a, b] : Site 2) ∈ box 2 m := by
  intro i
  fin_cases i
  · change a.natAbs ≤ m
    rcases Int.natAbs_eq a with h | h <;> omega
  · change b.natAbs ≤ m
    rcases Int.natAbs_eq b with h | h <;> omega


theorem fkSquareBoxPlanar_imageGraph_adj_iff (m : Nat) (x y : Site 2) :
    (imageGraph (fkSquareBoxPlanar m)).Adj x y ↔
      x ∈ box 2 m ∧ y ∈ box 2 m ∧ (hypercubicLattice 2).Adj x y := by
  rw [imageGraph_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨a.2, b.2, hab⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩


theorem sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner
    {N m : Nat} (hNm : N < m) {f g : Site 2}
    (hf : f ∈ box 2 N) (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge f g ∈ (imageGraph (fkSquareBoxPlanar m)).edgeSet := by
  have hf0 := hf 0
  have hf1 := hf 1
  have hb0 : -(m : Int) ≤ f 0 ∧ f 0 + 1 ≤ m := by
    rcases Int.natAbs_eq (f 0) with h | h <;> omega
  have hb1 : -(m : Int) ≤ f 1 ∧ f 1 + 1 ≤ m := by
    rcases Int.natAbs_eq (f 1) with h | h <;> omega
  rcases adj_cases hfg with ⟨h0, hfg1 | hgf1⟩ | ⟨h1, hfg0 | hgf0⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1], ![f 0 + 1, f 1]) := by
      unfold sharedPrimalEdge
      rw [if_pos h0, show max (f 1) (g 1) = f 1 by omega]
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds
        ⟨hb0.1, by omega⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨hb1.1, by omega⟩,
      by simpa using latAdj_right (f 0) (f 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1 + 1], ![f 0 + 1, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_pos h0, show max (f 1) (g 1) = g 1 by omega]
      congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨by omega, hb1.2⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_right (f 0) (f 1 + 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0, f 1], ![f 0, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_neg (by intro h; omega),
        show max (f 0) (g 0) = f 0 by omega]
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨hb0.1, by omega⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_top (f 0) (f 1)⟩
  · have he : sharedPrimalEdge f g =
        s(![f 0 + 1, f 1], ![f 0 + 1, f 1 + 1]) := by
      unfold sharedPrimalEdge
      rw [if_neg (by intro h; omega),
        show max (f 0) (g 0) = g 0 by omega]
      congr 1 <;> funext i <;> fin_cases i <;> simp <;> omega
    rw [he, SimpleGraph.mem_edgeSet,
      fkSquareBoxPlanar_imageGraph_adj_iff]
    exact ⟨site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨hb1.1, by omega⟩,
      site_mem_box_of_int_bounds ⟨by omega, hb0.2⟩ ⟨by omega, hb1.2⟩,
      by simpa using latAdj_top (f 0 + 1) (f 1)⟩


theorem fkSquareBox_innerFace_neighborSet_eq_empty
    {N m : Nat} (hNm : N < m) (f : Site 2) (hf : f ∈ box 2 N) :
    (whb_faceRegion (imageGraph (fkSquareBoxPlanar m))).neighborSet f = ∅ := by
  ext g
  constructor
  · intro hfg
    exact (hfg.2
      (sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner hNm hf hfg.1)).elim
  · simp


theorem pfdFace_eq_inner_iff
    {N m : Nat} (hNm : N < m) {f g : Site 2} (hg : g ∈ box 2 N) :
    pfdFace (fkSquareBoxPlanar m) f = pfdFace (fkSquareBoxPlanar m) g ↔ f = g := by
  constructor
  · intro hface
    have hreach : (whb_faceRegion (imageGraph (fkSquareBoxPlanar m))).Reachable f g :=
      ConnectedComponent.eq.mp hface
    by_contra hne
    exact (not_reachable_of_neighborSet_right_eq_empty hne
      (fkSquareBox_innerFace_neighborSet_eq_empty hNm g hg)) hreach
  · exact fun h => congrArg (pfdFace (fkSquareBoxPlanar m)) h


end
end StatMech.FrontierD
