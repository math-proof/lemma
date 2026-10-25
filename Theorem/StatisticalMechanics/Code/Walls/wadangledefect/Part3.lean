/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Def.StatisticalMechanics.Code.Walls.wadangledefect.Part3
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

theorem wad_edge_incident_cases {K : Finset Cell} {e : Sym2 Vtx} (he : e ∈ regEdges K)
    {v : Vtx} (hv : v ∈ e) :
    e = incidentEdgeR v ∨ e = incidentEdgeL v ∨ e = incidentEdgeU v ∨ e = incidentEdgeD v := by
  unfold regEdges at he
  rw [mem_biUnion] at he
  obtain ⟨c, _, hce⟩ := he
  obtain ⟨a, b⟩ := c; obtain ⟨x, y⟩ := v
  unfold cellEdges at hce
  simp only [mem_insert, mem_singleton] at hce
  simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD, Sym2.eq_iff,
    Prod.mk.injEq]
  rcases hce with h | h | h | h <;> subst h <;>
    simp only [Sym2.mem_iff, Prod.mk.injEq] at hv <;>
    obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) := hv <;> simp


theorem wad_incidentR_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeR v ∈ regEdges K ↔ (v ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeR
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    
    have hcell : ((a : ℤ) = x ∧ b = y) ∨ ((a : ℤ) = x ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hc
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentL_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeL v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ (v.1 - 1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeL
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y) ∨ ((a : ℤ) = x - 1 ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x - 1, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x - 1, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentU_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeU v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ v ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeU
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y) ∨ ((a : ℤ) = x ∧ b = y) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr hc
  · rintro (h | h)
    · refine ⟨(x - 1, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_incidentD_mem (K : Finset Cell) (v : Vtx) :
    incidentEdgeD v ∈ regEdges K ↔ ((v.1 - 1, v.2 - 1) ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
  obtain ⟨x, y⟩ := v
  unfold regEdges incidentEdgeD
  rw [mem_biUnion]
  constructor
  · rintro ⟨c, hc, hce⟩; obtain ⟨a, b⟩ := c
    unfold cellEdges at hce
    simp only [mem_insert, mem_singleton, Sym2.eq_iff, Prod.mk.injEq] at hce
    have hcell : ((a : ℤ) = x - 1 ∧ b = y - 1) ∨ ((a : ℤ) = x ∧ b = y - 1) := by
      rcases hce with h | h | h | h <;> omega
    rcases hcell with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · rintro (h | h)
    · refine ⟨(x - 1, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]
    · refine ⟨(x, y - 1), h, ?_⟩; unfold cellEdges
      simp [Sym2.eq_iff]


theorem wad_v_mem_incident (v : Vtx) :
    v ∈ incidentEdgeR v ∧ v ∈ incidentEdgeL v ∧ v ∈ incidentEdgeU v ∧ v ∈ incidentEdgeD v := by
  simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD]
  exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩


theorem wad_edgeDeg_eq (K : Finset Cell) (v : Vtx) :
    edgeDeg K v =
      (({incidentEdgeR v, incidentEdgeL v, incidentEdgeU v, incidentEdgeD v} : Finset (Sym2 Vtx)).filter
        (fun e => e ∈ regEdges K)).card := by
  classical
  unfold edgeDeg
  congr 1
  ext e
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨he, hv⟩
    exact ⟨wad_edge_incident_cases he hv, he⟩
  · rintro ⟨hcase, he⟩
    refine ⟨he, ?_⟩
    obtain ⟨mR, mL, mU, mD⟩ := wad_v_mem_incident v
    rcases hcase with h | h | h | h <;> (subst h; assumption)


theorem wad_defect_classify (K : Finset Cell) (v : Vtx) (hv : v ∈ regVerts K) :
    defect K v = 1 ∨ defect K v = 0 ∨ defect K v = -1 ∨ defect K v = -2 := by
  classical
  
  have hcellpos : 1 ≤ cellDeg K v := by
    unfold cellDeg
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    unfold regVerts at hv
    rw [mem_biUnion] at hv
    obtain ⟨c, hc, hvc⟩ := hv
    exact ⟨c, mem_inter.mpr ⟨(wad_mem_surround_iff v c).mpr hvc, hc⟩⟩
  obtain ⟨x, y⟩ := v
  
  have hcell : (cellDeg K (x, y) : ℤ) =
      (if ((x - 1, y - 1) ∈ K) then 1 else 0) + (if ((x, y - 1) ∈ K) then 1 else 0)
        + (if ((x - 1, y) ∈ K) then 1 else 0) + (if ((x, y) ∈ K) then 1 else 0) := by
    unfold cellDeg surroundCells
    dsimp only
    rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    have e1 : ((x:ℤ) - 1, y - 1) ∉ ({((x:ℤ), y - 1), (x - 1, y), (x, y)} : Finset Cell) := by
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega
    have e2 : ((x:ℤ), y - 1) ∉ ({((x:ℤ) - 1, y), (x, y)} : Finset Cell) := by
      simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega
    have e3 : ((x:ℤ) - 1, y) ∉ ({((x:ℤ), y)} : Finset Cell) := by
      simp only [mem_singleton, Prod.mk.injEq]; omega
    rw [Finset.sum_insert e1, Finset.sum_insert e2, Finset.sum_insert e3,
      Finset.sum_singleton]
    push_cast; ring
  
  have hedge : (edgeDeg K (x, y) : ℤ) =
      (if (((x, y) ∈ K) ∨ ((x, y - 1) ∈ K)) then 1 else 0)
        + (if (((x - 1, y) ∈ K) ∨ ((x - 1, y - 1) ∈ K)) then 1 else 0)
        + (if (((x - 1, y) ∈ K) ∨ ((x, y) ∈ K)) then 1 else 0)
        + (if (((x - 1, y - 1) ∈ K) ∨ ((x, y - 1) ∈ K)) then 1 else 0) := by
    rw [wad_edgeDeg_eq, Finset.card_filter]
    have i1 : incidentEdgeR (x, y) ∉
        ({incidentEdgeL (x, y), incidentEdgeU (x, y), incidentEdgeD (x, y)} :
          Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeR, incidentEdgeL, incidentEdgeU, incidentEdgeD, mem_insert,
        mem_singleton, Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_, ?_⟩ <;> omega
    have i2 : incidentEdgeL (x, y) ∉
        ({incidentEdgeU (x, y), incidentEdgeD (x, y)} : Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeL, incidentEdgeU, incidentEdgeD, mem_insert, mem_singleton,
        Sym2.eq_iff, Prod.mk.injEq]; push_neg; refine ⟨?_, ?_⟩ <;> omega
    have i3 : incidentEdgeU (x, y) ∉ ({incidentEdgeD (x, y)} : Finset (Sym2 Vtx)) := by
      simp only [incidentEdgeD, incidentEdgeU, mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
      push_neg; omega
    rw [Finset.sum_insert i1, Finset.sum_insert i2, Finset.sum_insert i3,
      Finset.sum_singleton]
    simp only [wad_incidentR_mem, wad_incidentL_mem, wad_incidentU_mem, wad_incidentD_mem]
    push_cast; ring
  
  have hcellposZ : (1 : ℤ) ≤ (cellDeg K (x, y) : ℤ) := by exact_mod_cast hcellpos
  rw [hcell] at hcellposZ
  clear hcellpos
  
  unfold defect
  rw [hcell, hedge]
  by_cases s1 : ((x - 1, y - 1) ∈ K) <;> by_cases s2 : ((x, y - 1) ∈ K) <;>
    by_cases s3 : ((x - 1, y) ∈ K) <;> by_cases s4 : ((x, y) ∈ K) <;>
    simp only [s1, s2, s3, s4, true_or, or_true, false_or, or_false,
      or_self, ↓reduceIte] at hcellposZ ⊢ <;> omega


end StatMech.Wad
