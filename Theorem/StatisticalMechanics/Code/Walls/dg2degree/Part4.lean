/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Def.StatisticalMechanics.Code.Walls.dg2degree.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem dg2_mem_pinchSet (p q : ℤ) :
    (![p, q] : Site 2) ∈ dg2_pinchSet ↔ (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 1) := by
  unfold dg2_pinchSet
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left; have h0 := congrFun h 0; have h1 := congrFun h 1
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using ⟨h0, h1⟩
    · right; have h0 := congrFun h 0; have h1 := congrFun h 1
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using ⟨h0, h1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left; rfl
    · right; rfl


theorem dg2_pinch_witness : (faceBoundaryGraph dg2_pinchSet).degree ![(0:ℤ), 0] = 4 := by
  rw [dg2_degree_eq_four_iff_checker]
  refine ⟨?_, ?_, ?_⟩
  · 
    simp only [show ((0:ℤ) + 1) = 1 from rfl]
    rw [dg2_mem_pinchSet, dg2_mem_pinchSet]; tauto
  · 
    simp only [show ((0:ℤ) + 1) = 1 from rfl]
    rw [dg2_mem_pinchSet, dg2_mem_pinchSet]
    constructor <;> (intro h; omega)
  · 
    simp only [show ((0:ℤ) + 1) = 1 from rfl]
    rw [dg2_mem_pinchSet, dg2_mem_pinchSet]
    constructor
    · intro _ h; omega
    · intro _; left; exact ⟨rfl, rfl⟩


theorem dg2_pinchSet_not_noPinch : ¬ dg2_NoPinch dg2_pinchSet := by
  intro h
  have h4 := dg2_pinch_witness
  rw [dg2_degree_eq_four_iff_checker] at h4
  exact h 0 0 h4


theorem dg2_pinch_bridges_out :
    (![(1:ℤ), 0] : Site 2) ∉ dg2_pinchSet ∧ (![(0:ℤ), 1] : Site 2) ∉ dg2_pinchSet := by
  constructor <;> (rw [dg2_mem_pinchSet]; omega)


theorem dg2_tromino_noPinch : dg2_NoPinch (↑pc2_tromino : Set (Site 2)) := by
  intro a b
  rw [dg2_Checker]
  
  rw [pc2_mem_tromino a b, pc2_mem_tromino (a+1) (b+1),
      pc2_mem_tromino (a+1) b, pc2_mem_tromino a (b+1)]
  
  
  rintro ⟨hd, ha, hf⟩
  omega


theorem dg2_tromino_corner_degree_eq_two :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).degree ![(-1:ℤ), -1] = 2 := by
  apply dg2_boundary_degree_eq_two dg2_tromino_noPinch
  
  exact ⟨_, pc2_trom_adj_1⟩


theorem dg2_boxPred_noPinch (x0 x1 y0 y1 : ℤ) :
    dg2_NoPinch {p : Site 2 | x0 ≤ p 0 ∧ p 0 ≤ x1 ∧ y0 ≤ p 1 ∧ p 1 ≤ y1} := by
  intro a b
  rw [dg2_Checker]
  simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  
  
  rintro ⟨hd, ha, hf⟩
  omega


theorem dg2_checker_iff_diagSplit (K : Set (Site 2)) (a b : ℤ) :
    dg2_Checker K a b ↔
      ((![a, b] : Site 2) ∈ K ∧ (![a + 1, b + 1] : Site 2) ∈ K ∧
        (![a + 1, b] : Site 2) ∉ K ∧ (![a, b + 1] : Site 2) ∉ K) ∨
      ((![a, b] : Site 2) ∉ K ∧ (![a + 1, b + 1] : Site 2) ∉ K ∧
        (![a + 1, b] : Site 2) ∈ K ∧ (![a, b + 1] : Site 2) ∈ K) := by
  unfold dg2_Checker
  by_cases h0 : (![a, b] : Site 2) ∈ K <;>
    by_cases h1 : (![a + 1, b] : Site 2) ∈ K <;>
    by_cases h2 : (![a + 1, b + 1] : Site 2) ∈ K <;>
    by_cases h3 : (![a, b + 1] : Site 2) ∈ K <;>
    simp_all


end Walls
end StatMech
