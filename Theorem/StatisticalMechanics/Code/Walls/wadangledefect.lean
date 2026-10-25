/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Def.StatisticalMechanics.Code.Walls.wadangledefect
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

theorem wad_mem_surround_iff (v : Vtx) (c : Cell) :
    c ∈ surroundCells v ↔ v ∈ cellVerts c := by
  obtain ⟨x, y⟩ := v; obtain ⟨a, b⟩ := c
  unfold surroundCells cellVerts
  simp only [mem_insert, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> omega


theorem wad_cellVerts_subset_regVerts {K : Finset Cell} {c : Cell} (hc : c ∈ K) :
    cellVerts c ⊆ regVerts K := by
  intro v hv; unfold regVerts; exact mem_biUnion.mpr ⟨c, hc, hv⟩


theorem wad_cellVerts_inter_regVerts {K : Finset Cell} {c : Cell} (hc : c ∈ K) :
    cellVerts c ∩ regVerts K = cellVerts c :=
  inter_eq_left.mpr (wad_cellVerts_subset_regVerts hc)


theorem wad_angleSum (K : Finset Cell) :
    ∑ v ∈ regVerts K, cellDeg K v = 4 * K.card := by
  classical
  have hcell : ∀ v ∈ regVerts K,
      cellDeg K v = ∑ c ∈ K, (if c ∈ surroundCells v then 1 else 0) := by
    intro v _
    unfold cellDeg
    rw [inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  rw [Finset.sum_congr rfl hcell, Finset.sum_comm]
  
  have hinner : ∀ c ∈ K,
      (∑ v ∈ regVerts K, if c ∈ surroundCells v then 1 else 0) = 4 := by
    intro c hc
    have : (∑ v ∈ regVerts K, if c ∈ surroundCells v then 1 else 0)
        = ((regVerts K).filter (fun v => c ∈ surroundCells v)).card := by
      rw [Finset.card_filter]
    rw [this]
    have hset : (regVerts K).filter (fun v => c ∈ surroundCells v) = cellVerts c := by
      ext v
      rw [mem_filter, wad_mem_surround_iff]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨wad_cellVerts_subset_regVerts hc h, h⟩
    rw [hset, euc_cellVerts_card]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring


theorem wad_edge_not_diag {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K) :
    ¬ e.IsDiag := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, _, hce⟩ := he
  obtain ⟨a, b⟩ := c
  unfold cellEdges at hce
  simp only [mem_insert, mem_singleton] at hce
  rcases hce with h | h | h | h <;>
    (subst h; rw [Sym2.mk_isDiag_iff]; simp only [Prod.mk.injEq, not_and]; omega)


theorem wad_edge_mem_regVerts {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K)
    {v : Vtx} (hv : v ∈ e) : v ∈ regVerts K := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, hc, hce⟩ := he
  apply wad_cellVerts_subset_regVerts hc
  obtain ⟨a, b⟩ := c
  unfold cellEdges at hce
  unfold cellVerts
  simp only [mem_insert, mem_singleton] at hce ⊢
  rcases hce with h | h | h | h <;>
    (subst h; rw [Sym2.mem_iff] at hv; obtain ⟨x, y⟩ := v;
     rcases hv with h | h <;> (rw [Prod.ext_iff] at h; simp only [Prod.mk.injEq]; omega))


theorem wad_endpoints_card {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K) :
    ((regVerts K).filter (fun v => v ∈ e)).card = 2 := by
  classical
  induction e with
  | h a b =>
    have hne : a ≠ b := by
      have h := wad_edge_not_diag he
      rw [Sym2.mk_isDiag_iff] at h; exact h
    have hset : (regVerts K).filter (fun v => v ∈ (s(a, b) : Sym2 Vtx)) = {a, b} := by
      ext v
      simp only [mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨_, h | h⟩ <;> [left; right] <;> exact h
      · rintro (h | h)
        · exact ⟨wad_edge_mem_regVerts he (h ▸ Sym2.mem_mk_left a b), Or.inl h⟩
        · exact ⟨wad_edge_mem_regVerts he (h ▸ Sym2.mem_mk_right a b), Or.inr h⟩
    rw [hset, card_insert_of_notMem (by simp [hne]), card_singleton]


theorem wad_edgeSum (K : Finset Cell) :
    ∑ v ∈ regVerts K, edgeDeg K v = 2 * (regEdges K).card := by
  classical
  have hedge : ∀ v ∈ regVerts K,
      edgeDeg K v = ∑ e ∈ regEdges K, (if v ∈ e then 1 else 0) := by
    intro v _; unfold edgeDeg; rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hedge, Finset.sum_comm]
  have hinner : ∀ e ∈ regEdges K,
      (∑ v ∈ regVerts K, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter]; exact wad_endpoints_card he
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  ring


end StatMech.Wad
