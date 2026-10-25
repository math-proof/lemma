/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Def.StatisticalMechanics.Code.Lattice.EulerFaces
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem mem_hEdges {n : ℕ} {e : Sym2 (Site 2)} :
    e ∈ hEdges n ↔ ∃ a b : ℤ, -(n : ℤ) ≤ a ∧ a < n ∧ -(n : ℤ) ≤ b ∧ b ≤ n ∧
      e = s(![a, b], ![a + 1, b]) := by
  unfold hEdges; rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc] at hp
    exact ⟨p.1, p.2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨(a, b), by
      rw [Finset.mem_product, Finset.mem_Ico, Finset.mem_Icc]; exact ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

theorem mem_vEdges {n : ℕ} {e : Sym2 (Site 2)} :
    e ∈ vEdges n ↔ ∃ a b : ℤ, -(n : ℤ) ≤ a ∧ a ≤ n ∧ -(n : ℤ) ≤ b ∧ b < n ∧
      e = s(![a, b], ![a, b + 1]) := by
  unfold vEdges; rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico] at hp
    exact ⟨p.1, p.2, hp.1.1, hp.1.2, hp.2.1, hp.2.2, rfl⟩
  · rintro ⟨a, b, h1, h2, h3, h4, rfl⟩
    exact ⟨(a, b), by
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Ico]; exact ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩


theorem mem_box2' {n : ℕ} {x : Site 2} :
    x ∈ box 2 n ↔ (x 0).natAbs ≤ n ∧ (x 1).natAbs ≤ n := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · intro h i; fin_cases i
    · exact h.1
    · exact h.2


theorem adj_box_mem_boxEdges (n : ℕ) {x y : Site 2} (hx : x ∈ box 2 n) (hy : y ∈ box 2 n)
    (hadj : (hypercubicLattice 2).Adj x y) : s(x, y) ∈ boxEdges n := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [mem_box2'] at hx hy
  have ex : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  have ey : y = ![y 0, y 1] := by funext i; fin_cases i <;> rfl
  rw [boxEdges, Finset.mem_union]
  by_cases hc1 : (x 1 - y 1).natAbs = 0
  · have he1 : x 1 = y 1 := by omega
    have hd0 : (x 0 - y 0).natAbs = 1 := by omega
    left; rw [mem_hEdges]
    rcases Int.natAbs_eq_iff.mp hd0 with h | h
    · refine ⟨y 0, y 1, by omega, by omega, by omega, by omega, ?_⟩
      rw [ex, ey, Sym2.eq_swap]; congr 1; funext i; fin_cases i <;> simp <;> omega
    · refine ⟨x 0, x 1, by omega, by omega, by omega, by omega, ?_⟩
      rw [ex, ey]; congr 1; funext i; fin_cases i <;> simp <;> omega
  · have hd1 : (x 1 - y 1).natAbs = 1 := by omega
    have he0 : x 0 = y 0 := by omega
    right; rw [mem_vEdges]
    rcases Int.natAbs_eq_iff.mp hd1 with h | h
    · refine ⟨y 0, y 1, by omega, by omega, by omega, by omega, ?_⟩
      rw [ex, ey, Sym2.eq_swap]; congr 1; funext i; fin_cases i <;> simp <;> omega
    · refine ⟨x 0, x 1, by omega, by omega, by omega, by omega, ?_⟩
      rw [ex, ey]; congr 1; funext i; fin_cases i <;> simp <;> omega


theorem mem_boxEdges_iff (n : ℕ) (x y : Site 2) :
    s(x, y) ∈ boxEdges n ↔
      x ∈ box 2 n ∧ y ∈ box 2 n ∧ (hypercubicLattice 2).Adj x y := by
  constructor
  · intro h
    rw [boxEdges, Finset.mem_union] at h
    rcases h with h | h
    · rw [mem_hEdges] at h
      obtain ⟨a, b, h1, h2, h3, h4, heq⟩ := h
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
        refine ⟨?_, ?_, ?_⟩ <;>
          first
          | (rw [mem_box2']; refine ⟨?_, ?_⟩ <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega)
          | (rw [hypercubicLattice_adj, Fin.sum_univ_two];
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
    · rw [mem_vEdges] at h
      obtain ⟨a, b, h1, h2, h3, h4, heq⟩ := h
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
        refine ⟨?_, ?_, ?_⟩ <;>
          first
          | (rw [mem_box2']; refine ⟨?_, ?_⟩ <;>
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> omega)
          | (rw [hypercubicLattice_adj, Fin.sum_univ_two];
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
  · rintro ⟨hx, hy, hadj⟩; exact adj_box_mem_boxEdges n hx hy hadj


theorem icc_card_n (n : ℕ) : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
  rw [Int.card_Icc]
  have : (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

theorem ico_card_n (n : ℕ) : (Finset.Ico (-(n : ℤ)) (n : ℤ)).card = 2 * n := by
  rw [Int.card_Ico]
  have : (n : ℤ) - -(n : ℤ) = ((2 * n : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]


theorem boxVerts_card (n : ℕ) : (boxVerts n).card = (2 * n + 1) ^ 2 := by
  unfold boxVerts
  rw [Finset.card_image_of_injective _ (fun p q h => by
    have h0 : (![p.1, p.2] : Site 2) 0 = (![q.1, q.2] : Site 2) 0 := by rw [h]
    have h1 : (![p.1, p.2] : Site 2) 1 = (![q.1, q.2] : Site 2) 1 := by rw [h]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1)]
  rw [Finset.card_product, icc_card_n, sq]


theorem hEdges_card (n : ℕ) : (hEdges n).card = (2 * n) * (2 * n + 1) := by
  unfold hEdges
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_product, ico_card_n, icc_card_n]
  · intro p q h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e0 : p.1 = q.1 := by have := congrFun h1 0; simpa using this
      have e1 : p.2 = q.2 := by have := congrFun h1 1; simpa using this
      exact Prod.ext e0 e1
    · have a0 : p.1 = q.1 + 1 := by have := congrFun h1 0; simpa using this
      have b0 : p.1 + 1 = q.1 := by have := congrFun h2 0; simpa using this
      omega


theorem vEdges_card (n : ℕ) : (vEdges n).card = (2 * n + 1) * (2 * n) := by
  unfold vEdges
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_product, icc_card_n, ico_card_n]
  · intro p q h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e0 : p.1 = q.1 := by have := congrFun h1 0; simpa using this
      have e1 : p.2 = q.2 := by have := congrFun h1 1; simpa using this
      exact Prod.ext e0 e1
    · have a0 : p.2 = q.2 + 1 := by have := congrFun h1 1; simpa using this
      have b0 : p.2 + 1 = q.2 := by have := congrFun h2 1; simpa using this
      omega


theorem hEdges_disjoint_vEdges (n : ℕ) : Disjoint (hEdges n) (vEdges n) := by
  rw [Finset.disjoint_left]
  intro e he hv
  rw [mem_hEdges] at he; rw [mem_vEdges] at hv
  obtain ⟨a, b, _, _, _, _, rfl⟩ := he
  obtain ⟨c, d, _, _, _, _, heq⟩ := hv
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1b : b = d := by have := congrFun h1 1; simpa using this
    have e2b : b = d + 1 := by have := congrFun h2 1; simpa using this
    omega
  · have e1b : b = d + 1 := by have := congrFun h1 1; simpa using this
    have e2b : b = d := by have := congrFun h2 1; simpa using this
    omega


theorem boxEdges_card (n : ℕ) : (boxEdges n).card = 2 * ((2 * n) * (2 * n + 1)) := by
  rw [boxEdges, Finset.card_union_of_disjoint (hEdges_disjoint_vEdges n),
    hEdges_card, vEdges_card]
  ring


theorem boxCells_card (n : ℕ) : (boxCells n).card = (2 * n) ^ 2 := by
  unfold boxCells
  rw [Finset.card_product, ico_card_n, sq]


end Lattice
end StatMech
