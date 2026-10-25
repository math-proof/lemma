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
import Instance.StatisticalMechanics.Code.Lattice.JordanEnclosure
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem latAdj_right (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_left (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_top (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]

theorem latAdj_bottom (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b - 1] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem candFinset_face (a b : ℤ) :
    candFinset 2 ![a, b] =
      ({![a + 1, b], ![a - 1, b], ![a, b + 1], ![a, b - 1]} : Finset (Site 2)) := by
  have huniv : (Finset.univ : Finset (Fin 2 × Bool))
      = {(0, true), (0, false), (1, true), (1, false)} := by decide
  unfold candFinset
  rw [huniv]
  simp only [Finset.image_insert, Finset.image_singleton]
  have e0 : candMap 2 ![a, b] (0, true) = ![a + 1, b] := by
    unfold candMap shift; funext i; fin_cases i <;> simp
  have e1 : candMap 2 ![a, b] (0, false) = ![a - 1, b] := by
    unfold candMap shift; funext i; fin_cases i <;> (simp; try ring)
  have e2 : candMap 2 ![a, b] (1, true) = ![a, b + 1] := by
    unfold candMap shift; funext i; fin_cases i <;> simp
  have e3 : candMap 2 ![a, b] (1, false) = ![a, b - 1] := by
    unfold candMap shift; funext i; fin_cases i <;> (simp; try ring)
  rw [e0, e1, e2, e3]

open Classical in


theorem neighborFinset_faceBoundaryGraph (S : Set (Site 2)) (f : Site 2) :
    (faceBoundaryGraph S).neighborFinset f =
      (candFinset 2 f).filter (fun g => (faceBoundaryGraph S).Adj f g) := by
  apply Finset.ext
  intro g
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  refine ⟨fun h => ⟨mem_candFinset_of_adj 2 f g (faceBoundaryGraph_le S h), h⟩, fun h => h.2⟩


theorem degree_faceBoundaryGraph (S : Set (Site 2)) (a b : ℤ) :
    (faceBoundaryGraph S).degree ![a, b] = faceBoundaryDegree S a b := by
  classical
  rw [SimpleGraph.degree, neighborFinset_faceBoundaryGraph, candFinset_face]
  have hr : (faceBoundaryGraph S).Adj ![a, b] ![a + 1, b]
      ↔ bdInd S (faceCorner10 a b) (faceCorner11 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_right, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_right a b)
  have hl : (faceBoundaryGraph S).Adj ![a, b] ![a - 1, b]
      ↔ bdInd S (faceCorner00 a b) (faceCorner01 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_left, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_left a b)
  have ht : (faceBoundaryGraph S).Adj ![a, b] ![a, b + 1]
      ↔ bdInd S (faceCorner01 a b) (faceCorner11 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_top, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_top a b)
  have hb : (faceBoundaryGraph S).Adj ![a, b] ![a, b - 1]
      ↔ bdInd S (faceCorner00 a b) (faceCorner10 a b) = 1 := by
    rw [faceBoundaryGraph_adj, sharedPrimalEdge_bottom, bdEdge_iff_bdInd]
    exact and_iff_right (latAdj_bottom a b)
  
  have d0 : ∀ x y : ℤ, x ≠ y → (![x, b] : Site 2) ≠ ![y, b] := by
    intro x y hxy h; apply hxy; have := congrFun h 0
    simpa only [Matrix.cons_val_zero] using this
  have d1 : ∀ x y : ℤ, x ≠ y → (![a, x] : Site 2) ≠ ![a, y] := by
    intro x y hxy h; apply hxy; have := congrFun h 1
    simpa only [Matrix.cons_val_one, Matrix.head_cons] using this
  have d12 : (![a + 1, b] : Site 2) ≠ ![a - 1, b] := d0 _ _ (by omega)
  have d13 : (![a + 1, b] : Site 2) ≠ ![a, b + 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d14 : (![a + 1, b] : Site 2) ≠ ![a, b - 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d23 : (![a - 1, b] : Site 2) ≠ ![a, b + 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d24 : (![a - 1, b] : Site 2) ≠ ![a, b - 1] := by
    intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  have d34 : (![a, b + 1] : Site 2) ≠ ![a, b - 1] := d1 _ _ (by omega)
  unfold faceBoundaryDegree
  rw [Finset.card_filter]
  rw [Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d12, d13, d14⟩),
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨d23, d24⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact d34),
      Finset.sum_singleton]
  have cast_ite : ∀ (P : Prop) [Decidable P] (n : ℕ), (P ↔ n = 1) → n ≤ 1 →
      (if P then 1 else 0) = n := by
    intro P _ n hPn _
    by_cases hP : P
    · rw [if_pos hP]; exact (hPn.mp hP).symm
    · rw [if_neg hP]
      have : n ≠ 1 := fun h => hP (hPn.mpr h)
      omega
  have hle : ∀ x y : Site 2, bdInd S x y ≤ 1 := by
    intro x y; unfold bdInd; by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]
  rw [cast_ite _ _ hr (hle _ _), cast_ite _ _ hl (hle _ _),
      cast_ite _ _ ht (hle _ _), cast_ite _ _ hb (hle _ _)]
  rw [bdInd_comm S (faceCorner00 a b) (faceCorner01 a b),
      bdInd_comm S (faceCorner01 a b) (faceCorner11 a b)]
  ring


theorem degree_faceBoundaryGraph_even (S : Set (Site 2)) (f : Site 2) :
    Even ((faceBoundaryGraph S).degree f) := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rw [hf, degree_faceBoundaryGraph]
  rw [Nat.even_iff]
  exact faceBoundaryDegree_even S (f 0) (f 1)


end Lattice
end StatMech
