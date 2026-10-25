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
import Def.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jce_phi_eq_odd_Hc (E : Finset (Sym2 (Site 2))) (c b : ℤ) :
    jce_phi E ![c, b] ↔ Odd (jce_Hc E c b) := by
  have h0 : (![c, b] : Site 2) 0 = c := rfl
  have h1 : (![c, b] : Site 2) 1 = b := rfl
  rw [jce_phi_def, jce_Hc, h0, h1]

theorem jce_Hc_succ (E : Finset (Sym2 (Site 2))) (c b : ℤ) :
    jce_Hc E c (b + 1) = jce_Hc E c b + (if s(![c, b + 1], ![c + 1, b + 1]) ∈ E then 1 else 0) := by
  rw [jce_Hc, jce_Hc]; exact jce_filter_succ_card E c b


theorem jce_degree_decomp (E : Finset (Sym2 (Site 2))) (a r : ℤ) :
    jce_degree (E : Set (Sym2 (Site 2))) ![a + 1, r] =
      (if s(![a + 1, r], ![a + 1 + 1, r]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a, r]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a + 1, r + 1]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a + 1, r - 1]) ∈ E then 1 else 0) := by
  classical
  unfold jce_degree jce_nbr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_coe]
  rw [Finset.card_filter, Fin.sum_univ_four]; norm_num


theorem jce_prop_const_of_step (Q : ℤ → Prop) (hstep : ∀ b, Q b ↔ Q (b + 1)) (b0 : ℤ)
    (hb0 : Q b0) : ∀ b, Q b := by
  have key : ∀ k : ℤ, Q (b0 + k) := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hb0
    | succ n ih => rw [show b0 + ((n : ℤ) + 1) = (b0 + n) + 1 by ring]; exact (hstep _).mp ih
    | pred n ih =>
        exact (hstep (b0 + (-(n : ℤ) - 1))).mpr
          (by rw [show b0 + (-(n : ℤ) - 1) + 1 = b0 + (-(n : ℤ)) by ring]; exact ih)
  intro b
  have := key (b - b0)
  rwa [show b0 + (b - b0) = b by ring] at this


theorem jce_Q_step (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) (a b : ℤ) :
    ((jce_Hc E a b + jce_Hc E (a + 1) b +
        (if s(![a + 1, b], ![a + 1, b + 1]) ∈ E then 1 else 0)) % 2 = 0) ↔
      ((jce_Hc E a (b + 1) + jce_Hc E (a + 1) (b + 1) +
        (if s(![a + 1, b + 1], ![a + 1, b + 1 + 1]) ∈ E then 1 else 0)) % 2 = 0) := by
  classical
  have hsa := jce_Hc_succ E a b
  have hsa1 := jce_Hc_succ E (a + 1) b
  have hdeg := hcc ![a + 1, b + 1]
  rw [jce_degree_decomp E a (b + 1), Nat.even_iff] at hdeg
  rw [show s(![a + 1, (b : ℤ) + 1], ![a, b + 1]) = s(![a, (b : ℤ) + 1], ![a + 1, b + 1]) from
        Sym2.eq_swap,
      show s(![a + 1, (b : ℤ) + 1], ![a + 1, b + 1 - 1]) = s(![a + 1, b], ![a + 1, b + 1]) by
        rw [show (b : ℤ) + 1 - 1 = b by ring, Sym2.eq_swap]] at hdeg
  rw [hsa, hsa1]
  set p1 := (if s(![a, (b : ℤ) + 1], ![a + 1, b + 1]) ∈ E then 1 else 0)
  set p2 := (if s(![a + 1, (b : ℤ) + 1], ![a + 1 + 1, b + 1]) ∈ E then 1 else 0)
  set p3 := (if s(![a + 1, (b : ℤ) + 1], ![a + 1, b + 1 + 1]) ∈ E then 1 else 0)
  set p4 := (if s(![a + 1, (b : ℤ)], ![a + 1, b + 1]) ∈ E then 1 else 0)
  omega


theorem jce_exists_lowRow (E : Finset (Sym2 (Site 2))) :
    ∃ L : ℤ, ∀ e ∈ E, ∀ x y : Site 2, e = s(x, y) → L ≤ x 1 ∧ L ≤ y 1 := by
  classical
  by_cases hE : E.Nonempty
  · refine ⟨(E.image (fun e => Sym2.lift ⟨fun x y => min (x 1) (y 1), by
      intro x y; simp only; rw [min_comm]⟩ e)).min' (hE.image _), ?_⟩
    intro e he x y hxy
    have hmin : (E.image (fun e => Sym2.lift ⟨fun x y => min (x 1) (y 1), by
        intro x y; simp only; rw [min_comm]⟩ e)).min' (hE.image _) ≤
          Sym2.lift ⟨fun x y => min (x 1) (y 1), by intro x y; simp only; rw [min_comm]⟩ e :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ he)
    subst hxy
    simp only [Sym2.lift_mk] at hmin
    exact ⟨le_trans hmin (min_le_left _ _), le_trans hmin (min_le_right _ _)⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    exact ⟨0, by simp [hE]⟩


theorem jce_Q_base (E : Finset (Sym2 (Site 2))) (a : ℤ) :
    ∃ b0 : ℤ, (jce_Hc E a b0 + jce_Hc E (a + 1) b0 +
      (if s(![a + 1, b0], ![a + 1, b0 + 1]) ∈ E then 1 else 0)) % 2 = 0 := by
  classical
  obtain ⟨L, hL⟩ := jce_exists_lowRow E
  refine ⟨L - 2, ?_⟩
  have hHc0 : ∀ c : ℤ, jce_Hc E c (L - 2) = 0 := by
    intro c
    rw [jce_Hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he
    induction e with
    | h x y =>
      rw [jce_horizBelow_mk]
      obtain ⟨hx, _⟩ := hL _ he x y rfl
      omega
  have hwall : s(![a + 1, L - 2], ![a + 1, L - 2 + 1]) ∉ E := by
    intro hmem
    obtain ⟨hx, _⟩ := hL _ hmem ![a + 1, L - 2] ![a + 1, L - 2 + 1] rfl
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hx
    omega
  rw [hHc0, hHc0, if_neg hwall]


theorem jce_horizStepResidue_holds : jce_HorizStepResidue := by
  classical
  intro E hcc a b
  obtain ⟨b0, hb0⟩ := jce_Q_base E a
  have hall := jce_prop_const_of_step
    (fun b => (jce_Hc E a b + jce_Hc E (a + 1) b +
      (if s(![a + 1, b], ![a + 1, b + 1]) ∈ E then 1 else 0)) % 2 = 0)
    (fun b => jce_Q_step E hcc a b) b0 hb0 b
  rw [jce_phi_eq_odd_Hc, jce_phi_eq_odd_Hc, Nat.odd_iff, Nat.odd_iff]
  by_cases hw : s(![a + 1, b], ![a + 1, b + 1]) ∈ E
  · rw [if_pos hw] at hall
    simp only [hw, true_iff]
    omega
  · rw [if_neg hw] at hall
    simp only [hw, false_iff, not_iff]
    omega


theorem jce_phi_compat (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) (a b : Site 2)
    (hab : (hypercubicLattice 2).Adj a b) :
    (sharedPrimalEdge a b ∈ (E : Set (Sym2 (Site 2))) ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
  classical
  have hab' := hab
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab'
  set a0 := a 0 with ha0; set a1 := a 1 with ha1
  set b0 := b 0 with hb0; set b1 := b 1 with hb1
  have ha : a = ![a0, a1] := by funext i; fin_cases i <;> rfl
  have hb : b = ![b0, b1] := by funext i; fin_cases i <;> rfl
  rw [Finset.mem_coe]
  
  rw [ha, hb]
  clear_value a0 a1 b0 b1
  clear ha hb ha0 ha1 hb0 hb1 hab
  by_cases hc0 : a0 = b0
  · 
    subst hc0
    have hc1 : a1 = b1 + 1 ∨ b1 = a1 + 1 := by omega
    rcases hc1 with h | h
    · 
      subst h
      have key := jce_phi_topStep E a0 b1
      rw [show sharedPrimalEdge ![a0, b1 + 1] ![a0, b1] = s(![a0, b1 + 1], ![a0 + 1, b1 + 1]) by
        rw [show (![a0, b1] : Site 2) = ![a0, (b1 + 1) - 1] by norm_num, sharedPrimalEdge_bottom]
        unfold faceCorner00 faceCorner10; norm_num]
      rw [key]; tauto
    · 
      subst h
      have key := jce_phi_topStep E a0 a1
      rw [show sharedPrimalEdge ![a0, a1] ![a0, a1 + 1] = s(![a0, a1 + 1], ![a0 + 1, a1 + 1]) by
        rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; norm_num]
      rw [key]
  · 
    have hc1 : a1 = b1 := by omega
    subst hc1
    have hc0' : a0 = b0 + 1 ∨ b0 = a0 + 1 := by omega
    rcases hc0' with h | h
    · 
      subst h
      have key := hres E hcc b0 a1
      rw [show sharedPrimalEdge ![b0 + 1, a1] ![b0, a1] = s(![b0 + 1, a1], ![b0 + 1, a1 + 1]) by
        rw [show (![b0, a1] : Site 2) = ![(b0 + 1) - 1, a1] by norm_num, sharedPrimalEdge_left]
        unfold faceCorner00 faceCorner01; norm_num]
      rw [key]; tauto
    · 
      subst h
      have key := hres E hcc a0 a1
      rw [show sharedPrimalEdge ![a0, a1] ![a0 + 1, a1] = s(![a0 + 1, a1], ![a0 + 1, a1 + 1]) by
        rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11; norm_num]
      rw [key]


end Lattice
end StatMech
