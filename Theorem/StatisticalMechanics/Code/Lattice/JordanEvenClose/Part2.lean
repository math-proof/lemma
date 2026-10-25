/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Def.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

open Classical in
theorem jce_phi_def (E : Finset (Sym2 (Site 2))) (f : Site 2) :
    jce_phi E f ↔ Odd (E.filter (fun e => jce_horizBelow (f 0) (f 1) e)).card :=
  Iff.rfl


theorem jce_site_eq_iff (x : Site 2) (c d : ℤ) : x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp_all


theorem jce_horizBelow_succ (a b : ℤ) (e : Sym2 (Site 2)) :
    jce_horizBelow a (b + 1) e ↔
      (jce_horizBelow a b e ∨ e = s(![a, b + 1], ![a + 1, b + 1])) := by
  induction e with
  | h x y =>
    rw [jce_horizBelow_mk, jce_horizBelow_mk, Sym2.eq_iff, jce_site_eq_iff, jce_site_eq_iff,
      jce_site_eq_iff, jce_site_eq_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_eq_of_le h2 with hlt | heq
      · exact Or.inl ⟨h1, by omega, h3⟩
      · rcases h3 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inr (Or.inl ⟨⟨hx, by omega⟩, ⟨hy, by omega⟩⟩)
        · exact Or.inr (Or.inr ⟨⟨hx, by omega⟩, ⟨hy, by omega⟩⟩)
    · rintro (⟨h1, h2, h3⟩ | ⟨⟨hx0, hx1⟩, hy0, hy1⟩ | ⟨⟨hx0, hx1⟩, hy0, hy1⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨by omega, by omega, Or.inl ⟨hx0, hy0⟩⟩
      · exact ⟨by omega, by omega, Or.inr ⟨hx0, hy0⟩⟩


theorem jce_succEdge_not_below (a b : ℤ) :
    ¬ jce_horizBelow a b s(![a, b + 1], ![a + 1, b + 1]) := by
  rw [jce_horizBelow_mk]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

open Classical in


theorem jce_filter_succ_card (E : Finset (Sym2 (Site 2))) (a b : ℤ) :
    (E.filter (fun e => jce_horizBelow a (b + 1) e)).card =
      (E.filter (fun e => jce_horizBelow a b e)).card +
        (if s(![a, b + 1], ![a + 1, b + 1]) ∈ E then 1 else 0) := by
  classical
  set edge := s(![a, b + 1], ![a + 1, b + 1]) with hedge
  have hsub : E.filter (fun e => jce_horizBelow a b e) ⊆
      E.filter (fun e => jce_horizBelow a (b + 1) e) := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, (jce_horizBelow_succ a b e).mpr (Or.inl he.2)⟩
  have hdiff : (E.filter (fun e => jce_horizBelow a (b + 1) e)) \
      (E.filter (fun e => jce_horizBelow a b e)) =
      if edge ∈ E then {edge} else ∅ := by
    ext e
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    by_cases hin : edge ∈ E
    · rw [if_pos hin, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨he, hb1⟩, hnb⟩
        rcases (jce_horizBelow_succ a b e).mp hb1 with hb | hb
        · exact absurd ⟨he, hb⟩ hnb
        · exact hb
      · rintro rfl
        exact ⟨⟨hin, (jce_horizBelow_succ a b edge).mpr (Or.inr rfl)⟩,
          fun h => jce_succEdge_not_below a b h.2⟩
    · rw [if_neg hin]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨he, hb1⟩, hnb⟩
      rcases (jce_horizBelow_succ a b e).mp hb1 with hb | hb
      · exact hnb ⟨he, hb⟩
      · subst hb; exact hin he
  have hcardeq := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff] at hcardeq
  by_cases hin : edge ∈ E
  · rw [if_pos hin, Finset.card_singleton] at hcardeq
    rw [if_pos hin]; omega
  · rw [if_neg hin, Finset.card_empty] at hcardeq
    rw [if_neg hin]; omega


theorem jce_phi_topStep (E : Finset (Sym2 (Site 2))) (a b : ℤ) :
    (s(![a, b + 1], ![a + 1, b + 1]) ∈ E ↔
      (jce_phi E ![a, b] ↔ ¬ jce_phi E ![a, b + 1])) := by
  classical
  rw [jce_phi_def, jce_phi_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [jce_filter_succ_card E a b]
  set n := (E.filter (fun e => jce_horizBelow a b e)).card with hn
  by_cases hin : s(![a, b + 1], ![a + 1, b + 1]) ∈ E
  · rw [if_pos hin]
    simp only [hin, Nat.odd_add_one, not_not]
  · rw [if_neg hin]
    simp only [hin, false_iff, add_zero, not_iff]


end Lattice
end StatMech
