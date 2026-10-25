/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.CellEulerFaithful


namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


theorem regEdge_mem_imageGraph (S : Finset Cell) {e : Sym2 Vtx}
    (he : e ∈ StatMech.Euc.regEdges S) :
    Sym2.map (fun v : Vtx => ![v.1, v.2]) e ∈ (imageGraph (cellSkeletonP S)).edgeSet := by
  induction e with
  | h a b =>
      have ha : a ∈ regVerts S := wad_edge_mem_regVerts he (by simp)
      have hb : b ∈ regVerts S := wad_edge_mem_regVerts he (by simp)
      simp only [Sym2.map_mk]
      rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, he, rfl, rfl⟩


theorem sharedPrimalEdge_mem_regEdges (S : Finset Cell) (c : Cell) (hc : c ∈ S)
    (g : Site 2) (hlat : (hypercubicLattice 2).Adj (cellFace c) g) :
    Sym2.map cellFace.symm (sharedPrimalEdge (cellFace c) g) ∈
      StatMech.Euc.regEdges S := by
  obtain ⟨x, y⟩ := c
  have hdist := hlat
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hdist
  simp only [cellFace_zero, cellFace_one] at hdist
  have hcases : g = ![x + 1, y] ∨ g = ![x - 1, y] ∨
      g = ![x, y + 1] ∨ g = ![x, y - 1] := by
    by_cases hx : g 0 = x
    · have hy : g 1 = y + 1 ∨ g 1 = y - 1 := by
        have : (y - g 1).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hy with hy | hy
      · right; right; left
        funext i; fin_cases i <;> simp [hx, hy]
      · right; right; right
        funext i; fin_cases i <;> simp [hx, hy]
    · have hy : g 1 = y := by omega
      have hx' : g 0 = x + 1 ∨ g 0 = x - 1 := by
        have : (x - g 0).natAbs = 1 := by omega
        rcases Int.natAbs_eq_iff.mp this with h | h <;> omega
      rcases hx' with hx' | hx'
      · left; funext i; fin_cases i <;> simp [hx', hy]
      · right; left; funext i; fin_cases i <;> simp [hx', hy]
  rw [StatMech.Euc.regEdges, Finset.mem_biUnion]
  refine ⟨(x, y), hc, ?_⟩
  rcases hcases with rfl | rfl | rfl | rfl
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x + 1, y]) ∈ _
    rw [sharedPrimalEdge_right]
    simp [Sym2.map_mk, StatMech.Euc.cellEdges, faceCorner10, faceCorner11]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x - 1, y]) ∈ _
    rw [sharedPrimalEdge_left]
    simp [Sym2.map_mk, StatMech.Euc.cellEdges, faceCorner00, faceCorner01]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x, y + 1]) ∈ _
    rw [sharedPrimalEdge_top]
    simp [Sym2.map_mk, StatMech.Euc.cellEdges, faceCorner01, faceCorner11]
  · change Sym2.map cellFace.symm (sharedPrimalEdge ![x, y] ![x, y - 1]) ∈ _
    rw [sharedPrimalEdge_bottom]
    simp [Sym2.map_mk, StatMech.Euc.cellEdges, faceCorner00, faceCorner10]


theorem occupiedFace_isolated (S : Finset Cell) (c : Cell) (hc : c ∈ S) (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph (cellSkeletonP S))).Adj (cellFace c) g := by
  intro hadj
  rw [whb_faceRegion_adj] at hadj
  apply hadj.2
  have he := sharedPrimalEdge_mem_regEdges S c hc g hadj.1
  have himg := regEdge_mem_imageGraph S he
  generalize hedge : sharedPrimalEdge (cellFace c) g = e at he himg ⊢
  induction e with
  | h a b =>
      simp only [Sym2.map_mk] at himg ⊢
      convert himg using 1
      rw [Sym2.eq_iff]
      left
      constructor <;> funext i <;> fin_cases i <;> rfl


end StatMech.Onsager.CellEulerFaithful
