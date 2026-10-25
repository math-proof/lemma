/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Young.YoungDiagram
import Def.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula
set_option autoImplicit false

open scoped Nat


lemma HasseWalkFormula.hasseWalk_card_le {m : ℕ}
    (walk : Fin (m + 1) → YoungDiagram)
    (hstart : walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hstep : ∀ i : Fin m,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (k : ℕ) (hk : k ≤ m) :
    (walk ⟨k, Nat.lt_succ_of_le hk⟩).card ≤ k := by
  induction k with
  | zero =>
    simp only [hstart, YoungDiagram.card]
    simp
  | succ p ih =>
    have hp_le : p ≤ m := Nat.le_of_succ_le hk
    have hp_lt : p < m := Nat.lt_of_succ_le hk
    have hp_eq : (⟨p, Nat.lt_succ_of_lt hp_lt⟩ : Fin (m + 1)) =
        ⟨p, Nat.lt_succ_of_le hp_le⟩ := rfl
    have hp1_eq : (⟨p + 1, Nat.succ_lt_succ hp_lt⟩ : Fin (m + 1)) =
        ⟨p + 1, Nat.lt_succ_of_le hk⟩ := rfl
    rcases hstep ⟨p, hp_lt⟩ with hup | hdown
    · have h_card := HasseWalks.card_covBy_succ hup
      rw [hp_eq, hp1_eq] at h_card
      have := ih hp_le
      omega
    · have h_card := HasseWalks.card_covBy_succ hdown
      rw [hp_eq, hp1_eq] at h_card
      have := ih hp_le
      omega

lemma HasseWalkFormula.yd_cell_bounded (yd : YoungDiagram) (i j : ℕ)
    (h : (i, j) ∈ yd.cells) : i < yd.card ∧ j < yd.card := by
  constructor
  · have hmem : ∀ i' : ℕ, i' ≤ i → (i', 0) ∈ yd.cells :=
      fun i' hi' => yd.isLowerSet (Prod.mk_le_mk.mpr ⟨hi', Nat.zero_le _⟩) h
    have hsub : Finset.image (fun i' => (i', 0)) (Finset.range (i + 1)) ⊆ yd.cells := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨i', hi', rfl⟩ := hx
      exact hmem i' (by rw [Finset.mem_range] at hi'; omega)
    have hc : (Finset.image (fun i' => (i', 0)) (Finset.range (i + 1))).card = i + 1 := by
      rw [Finset.card_image_of_injective _ (by intro a b hab; exact (Prod.mk.inj hab).1)]
      exact Finset.card_range _
    have := Finset.card_le_card hsub; simp only [YoungDiagram.card]; omega
  · have hmem : ∀ j' : ℕ, j' ≤ j → (0, j') ∈ yd.cells :=
      fun j' hj' => yd.isLowerSet (Prod.mk_le_mk.mpr ⟨Nat.zero_le _, hj'⟩) h
    have hsub : Finset.image (fun j' => (0, j')) (Finset.range (j + 1)) ⊆ yd.cells := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨j', hj', rfl⟩ := hx
      exact hmem j' (by rw [Finset.mem_range] at hj'; omega)
    have hc : (Finset.image (fun j' => (0, j')) (Finset.range (j + 1))).card = j + 1 := by
      rw [Finset.card_image_of_injective _ (by intro a b hab; exact (Prod.mk.inj hab).2)]
      exact Finset.card_range _
    have := Finset.card_le_card hsub; simp only [YoungDiagram.card]; omega

lemma HasseWalkFormula.yd_cells_sub_grid {yd : YoungDiagram} {n : ℕ} (hn : yd.card ≤ n) :
    yd.cells ⊆ Finset.range n ×ˢ Finset.range n := by
  intro ⟨i, j⟩ hij
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨Nat.lt_of_lt_of_le (yd_cell_bounded yd i j hij).1 hn,
         Nat.lt_of_lt_of_le (yd_cell_bounded yd i j hij).2 hn⟩

lemma HasseWalkFormula.hasseWalkType_cells_bounded {m : ℕ}
    (w : Fin (m + 1) → YoungDiagram)
    (h0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hs : ∀ i : Fin m,
      w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (k : Fin (m + 1)) :
    (w k).cells ⊆ Finset.range m ×ˢ Finset.range m := by
  obtain ⟨k, hk⟩ := k
  apply yd_cells_sub_grid
  have := hasseWalk_card_le w h0 hs k (by omega)
  omega

