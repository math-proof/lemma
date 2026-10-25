/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Def.StatisticalMechanics.Code.Onsager.CellEulerBound


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


@[simp] theorem edgeCode_mk (a b : ℤ × ℤ) :
    edgeCode s(a, b) = (a.1 + b.1, a.2 + b.2) := rfl


theorem image_cellEdges_edgeCode (c : Cell) :
    (StatMech.Euc.cellEdges c).image edgeCode = edgesOf c := by
  obtain ⟨x, y⟩ := c
  ext e
  simp only [StatMech.Euc.cellEdges, edgesOf, mem_image, mem_insert, mem_singleton,
    edgeCode_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨z, (rfl | rfl | rfl | rfl), rfl⟩ <;> simp <;> omega
  · rintro (rfl | rfl | rfl | rfl)
    · refine ⟨s(((x, y)), ((x + 1, y))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      constructor <;> omega
    · refine ⟨s(((x, y + 1)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega
    · refine ⟨s(((x, y)), ((x, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega
    · refine ⟨s(((x + 1, y)), ((x + 1, y + 1))), by simp, ?_⟩
      simp only [edgeCode_mk, Prod.mk.injEq]
      congr 1 <;> omega


theorem image_regEdges_edgeCode (S : Finset Cell) :
    (regEdges S).image edgeCode = StatMech.Onsager.CellEuler.cellEdges S := by
  ext e
  rw [mem_image, StatMech.Onsager.CellEuler.cellEdges, mem_biUnion]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [regEdges, mem_biUnion] at hz
    obtain ⟨c, hc, hzc⟩ := hz
    refine ⟨c, hc, ?_⟩
    have hz : edgeCode z ∈ (StatMech.Euc.cellEdges c).image edgeCode :=
      mem_image.mpr ⟨z, hzc, rfl⟩
    rwa [image_cellEdges_edgeCode] at hz
  · rintro ⟨c, hc, hec⟩
    have he : e ∈ (StatMech.Euc.cellEdges c).image edgeCode := by
      rwa [image_cellEdges_edgeCode]
    obtain ⟨z, hzc, rfl⟩ := mem_image.mp he
    refine ⟨z, ?_, rfl⟩
    rw [regEdges, mem_biUnion]
    exact ⟨c, hc, hzc⟩


theorem edgeCode_injOn_regEdges (S : Finset Cell) :
    Set.InjOn edgeCode (regEdges S) := by
  intro e he f hf hef
  have he' : e ∈ regEdges S := he
  have hf' : f ∈ regEdges S := hf
  simp only [regEdges, mem_biUnion] at he' hf'
  obtain ⟨c, -, hec⟩ := he'
  obtain ⟨d, -, hfd⟩ := hf'
  obtain ⟨x, y⟩ := c
  obtain ⟨u, v⟩ := d
  simp only [StatMech.Euc.cellEdges, mem_insert, mem_singleton] at hec hfd
  rcases hec with rfl | rfl | rfl | rfl <;>
    rcases hfd with rfl | rfl | rfl | rfl <;>
    simp only [edgeCode_mk, Prod.mk.injEq] at hef <;>
    rw [Sym2.eq_iff] <;>
    simp only [Prod.mk.injEq] <;>
    omega


theorem card_cellEdges_eq_regEdges (S : Finset Cell) :
    (StatMech.Onsager.CellEuler.cellEdges S).card = (regEdges S).card := by
  rw [← image_regEdges_edgeCode S, card_image_iff.mpr]
  intro e he f hf h
  exact edgeCode_injOn_regEdges S he hf h


theorem cellVerts_eq_regVerts (S : Finset Cell) :
    StatMech.Onsager.CellCount.cellVerts S = regVerts S := by
  ext v
  simp only [StatMech.Onsager.CellCount.cellVerts, regVerts, mem_biUnion]
  constructor
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.Euc.cellVerts, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv ⊢
    omega
  · rintro ⟨c, hc, hv⟩
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, y⟩ := c
    simp only [cornersOf, StatMech.Euc.cellVerts, mem_insert, mem_singleton,
      Prod.mk.injEq] at hv ⊢
    omega


theorem eulerChar_eq_regChi (S : Finset Cell) : eulerChar S = regChi S := by
  unfold eulerChar regChi
  rw [cellVerts_eq_regVerts, card_cellEdges_eq_regEdges]


end StatMech.Onsager.CellEulerBound
