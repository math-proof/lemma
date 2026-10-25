/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.Walls.bcorcorridors
open Set SimpleGraph
open StatMech StatMech.Lattice


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

set_option maxHeartbeats 800000


theorem bcor_rot90_mem_box {n : ℕ} {x : Site 2} (hx : x ∈ box 2 n) :
    rot90Fun x ∈ box 2 n := by
  rw [mem_box] at hx ⊢
  intro i
  fin_cases i
  · simpa [rot90Fun] using hx 1
  · simpa [rot90Fun] using hx 0


theorem bcor_corridors_rot90 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    bcor_Corridors n (rot90Fun u₁) (rot90Fun u₂) (rot90Fun u₃) := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  have hstart : rot90Fun ![0, 0] = (![0, 0] : Site 2) := by
    rw [rot90Fun_apply]
    rfl
  let M₁ := P₁.map rot90Iso.toHom
  let M₂ := P₂.map rot90Iso.toHom
  let M₃ := P₃.map rot90Iso.toHom
  let Q₁ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₁) := M₁.copy hstart rfl
  let Q₂ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₂) := M₂.copy hstart rfl
  let Q₃ : (hypercubicLattice 2).Walk ![0, 0] (rot90Fun u₃) := M₃.copy hstart rfl
  have hq1 : Q₁.IsPath := by
    simpa [Q₁, M₁, Walk.isPath_copy] using
      P₁.map_isPath_of_injective rot90Iso.injective hp1
  have hq2 : Q₂.IsPath := by
    simpa [Q₂, M₂, Walk.isPath_copy] using
      P₂.map_isPath_of_injective rot90Iso.injective hp2
  have hq3 : Q₃.IsPath := by
    simpa [Q₃, M₃, Walk.isPath_copy] using
      P₃.map_isPath_of_injective rot90Iso.injective hp3
  refine ⟨Q₁, Q₂, Q₃, hq1, hq2, hq3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb1 x hx)
  · intro z hz
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb2 x hx)
  · intro z hz
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact bcor_rot90_mem_box (hb3 x hx)
  · intro z hz1 hz2
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz2
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd12 x hx hy)
  · intro z hz1 hz3
    simp only [Q₁, M₁, Walk.support_copy, Walk.support_map, List.mem_map] at hz1
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz1
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd13 x hx hy)
  · intro z hz2 hz3
    simp only [Q₂, M₂, Walk.support_copy, Walk.support_map, List.mem_map] at hz2
    simp only [Q₃, M₃, Walk.support_copy, Walk.support_map, List.mem_map] at hz3
    obtain ⟨x, hx, rfl⟩ := hz2
    obtain ⟨y, hy, heq⟩ := hz3
    have hxy : x = y := rot90Equiv.injective (by
      simpa [rot90Equiv_apply] using heq.symm)
    subst y
    simpa [rot90Fun_apply] using congrArg rot90Fun (hd23 x hx hy)


theorem bcor_corridors_rot90_iterate (k : ℕ) {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) :
    bcor_Corridors n ((rot90Fun^[k]) u₁) ((rot90Fun^[k]) u₂)
      ((rot90Fun^[k]) u₃) := by
  induction k with
  | zero => simpa using hC
  | succ k ih =>
      simpa [Function.iterate_succ_apply'] using bcor_corridors_rot90 ih


theorem bcor_corridors_swap12 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) : bcor_Corridors n u₂ u₁ u₃ := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  refine ⟨P₂, P₁, P₃, hp2, hp1, hp3, hb2, hb1, hb3, ?_, ?_, ?_⟩
  · intro z hz2 hz1
    exact hd12 z hz1 hz2
  · exact hd23
  · exact hd13


theorem bcor_corridors_swap23 {n : ℕ} {u₁ u₂ u₃ : Site 2}
    (hC : bcor_Corridors n u₁ u₂ u₃) : bcor_Corridors n u₁ u₃ u₂ := by
  obtain ⟨P₁, P₂, P₃, hp1, hp2, hp3, hb1, hb2, hb3, hd12, hd13, hd23⟩ := hC
  refine ⟨P₁, P₃, P₂, hp1, hp3, hp2, hb1, hb3, hb2, hd13, hd12, ?_⟩
  intro z hz3 hz2
  exact hd23 z hz2 hz3


end StatMech.Walls
