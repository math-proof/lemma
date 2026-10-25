/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal.Part2
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shb_mem_paritySupportOn
    {E : Type*} [DecidableEq E] (S : Finset E) (m : ↑S → ℕ)
    (e : ↑S) :
    e.1 ∈ shbParitySupportOn S m ↔ Odd (m e) := by
  simp [shbParitySupportOn]

theorem shb_paritySupportOn_eq_iff
    {E : Type*} [DecidableEq E] (S A : Finset E) (hAS : A ⊆ S)
    (m : ↑S → ℕ) :
    shbParitySupportOn S m = A ↔
      ∀ e : ↑S, if e.1 ∈ A then Odd (m e) else Even (m e) := by
  constructor
  · intro h e
    by_cases he : e.1 ∈ A
    · simp only [if_pos he]
      rw [← h] at he
      simpa using he
    · simp only [if_neg he]
      rw [← Nat.not_odd_iff_even]
      intro ho
      apply he
      rw [← h]
      simpa using ho
  · intro h
    ext e
    by_cases heS : e ∈ S
    · let es : ↑S := ⟨e, heS⟩
      change (es.1 ∈ shbParitySupportOn S m ↔ e ∈ A)
      rw [shb_mem_paritySupportOn]
      by_cases heA : e ∈ A
      · have ho : Odd (m es) := by simpa [es, heA] using h es
        simp [heA, ho]
      · have hev : Even (m es) := by simpa [es, heA] using h es
        rw [← Nat.not_odd_iff_even] at hev
        simp [heA, hev]
    · have heA : e ∉ A := fun he => heS (hAS he)
      simp [shbParitySupportOn, heS, heA]

theorem shb_fixedParity_tsum
    {E : Type*} [DecidableEq E] (S A : Finset E) (hAS : A ⊆ S)
    (x : ℝ) (hx : 0 ≤ x) :
    (∑' m : ↑S → ℕ,
      if shbParitySupportOn S m = A then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
      ∏ e ∈ S,
        if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x := by
  let g : E → ℕ → ℝ := fun e k =>
    if (if e ∈ A then Odd k else Even k) then shbCurrentTerm x k else 0
  have hgsum : ∀ e, Summable (g e) := by
    intro e
    unfold g
    exact shb_summable_currentTerm_filter x _
  have hgnn : ∀ e k, 0 ≤ g e k := by
    intro e k
    by_cases h : if e ∈ A then Odd k else Even k
    · simp only [g, h, if_true]
      exact div_nonneg (pow_nonneg hx _) (by positivity)
    · simp [g, h]
  calc
    (∑' m : ↑S → ℕ,
        if shbParitySupportOn S m = A then
          ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
        ∑' m : ↑S → ℕ, ∏ e : ↑S, g e.1 (m e) := by
      apply tsum_congr
      intro m
      by_cases hs : shbParitySupportOn S m = A
      · rw [if_pos hs]
        have hall := (shb_paritySupportOn_eq_iff S A hAS m).mp hs
        apply Finset.prod_congr rfl
        intro e _
        simp only [g]
        rw [if_pos (hall e)]
      · rw [if_neg hs]
        have hall : ¬ ∀ e : ↑S,
            if e.1 ∈ A then Odd (m e) else Even (m e) :=
          fun h => hs ((shb_paritySupportOn_eq_iff S A hAS m).mpr h)
        push Not at hall
        obtain ⟨e, he⟩ := hall
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        simp only [g]
        rw [if_neg he]
    _ = ∏ e ∈ S, ∑' k : ℕ, g e k :=
      (prod_tsum_fubini g hgsum hgnn S).2.symm
    _ = ∏ e ∈ S,
          if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x := by
      apply Finset.prod_congr rfl
      intro e heS
      by_cases heA : e ∈ A
      · simp only [g, heA, if_true]
        exact shb_tsum_odd_filter x
      · simp only [g, heA, if_false]
        exact shb_tsum_even_filter x


theorem shb_current_tsum_eq_paritySeriesMassOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P]
    (x : ℝ) (hx : 0 ≤ x) :
    (∑' m : ↑S → ℕ,
      if P (shbParitySupportOn S m) then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
      shbParitySeriesMassOn S P x := by
  unfold shbParitySeriesMassOn
  let F : Finset E → (↑S → ℕ) → ℝ := fun A m =>
    if P A then
      if shbParitySupportOn S m = A then
        ∏ e : ↑S, shbCurrentTerm x (m e) else 0
    else 0
  have hFsum : ∀ A ∈ S.powerset, Summable (F A) := by
    intro A hAS
    by_cases hPA : P A
    · simp only [F, hPA, if_true]
      refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
        (prod_tsum_fubini (fun _ k => shbCurrentTerm x k)
          (fun _ => shb_summable_currentTerm x)
          (fun _ k => div_nonneg (pow_nonneg hx _) (by positivity)) S).1
      · split
        · exact Finset.prod_nonneg (fun _ _ =>
            div_nonneg (pow_nonneg hx _) (by positivity))
        · exact le_rfl
      · split
        · exact le_rfl
        · exact Finset.prod_nonneg (fun _ _ =>
            div_nonneg (pow_nonneg hx _) (by positivity))
    · simp [F, hPA]
  calc
    (∑' m : ↑S → ℕ,
        if P (shbParitySupportOn S m) then
          ∏ e : ↑S, shbCurrentTerm x (m e) else 0) =
        ∑' m : ↑S → ℕ, ∑ A ∈ S.powerset, F A m := by
      apply tsum_congr
      intro m
      let A := shbParitySupportOn S m
      rw [Finset.sum_eq_single A]
      · simp [F, A]
      · intro B hB hBA
        by_cases hPB : P B
        · simp only [F, hPB, if_true]
          rw [if_neg]
          intro heq
          exact hBA heq.symm
        · simp [F, hPB]
      · intro hA
        exact absurd (Finset.mem_powerset.mpr (by
          intro e he
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
          exact a.2)) hA
    _ = ∑ A ∈ S.powerset, ∑' m : ↑S → ℕ, F A m :=
      Summable.tsum_finsetSum hFsum
    _ = ∑ A ∈ S.powerset,
          if P A then
            ∏ e ∈ S,
              if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
          else 0 := by
      apply Finset.sum_congr rfl
      intro A hAS
      by_cases hPA : P A
      · simp only [F, hPA, if_true]
        exact shb_fixedParity_tsum S A (Finset.mem_powerset.mp hAS) x hx
      · simp [F, hPA]


end StatMech.Sharpness
