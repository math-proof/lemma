/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding.Part2
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in
lemma prefixIdx_zero (n : ℕ) : prefixIdx n 0 = ∅ := by
  unfold prefixIdx; apply Finset.filter_false_of_mem; intro s _; omega

omit [Fintype E] in
lemma prefixIdx_succ_lt (n t : ℕ) (ht : t < n) :
    prefixIdx n (t+1) = insert (⟨t, ht⟩ : Fin n) (prefixIdx n t) := by
  unfold prefixIdx; ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hs; rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · exact Or.inr h
    · left; exact Fin.ext h
  · rintro (rfl | h)
    · exact Nat.lt_succ_self t
    · exact Nat.lt_succ_of_lt h

omit [Fintype E] in
lemma prefixIdx_ge (n t : ℕ) (ht : n ≤ t) : prefixIdx n t = Finset.univ := by
  unfold prefixIdx; apply Finset.filter_true_of_mem; intro s _; exact lt_of_lt_of_le s.2 ht

omit [Fintype E] in
lemma prefixIdx_self (n : ℕ) : prefixIdx n n = Finset.univ := prefixIdx_ge n n le_rfl

omit [Fintype E] in
lemma prefixIdx_succ_ge (n t : ℕ) (ht : n ≤ t) : prefixIdx n (t+1) = prefixIdx n t := by
  rw [prefixIdx_ge n t ht, prefixIdx_ge n (t+1) (by omega)]

omit [Fintype E] in
lemma mem_prefixIdx_lt (n t : ℕ) (ht : t < n) : (⟨t, ht⟩ : Fin n) ∉ prefixIdx n t := by
  unfold prefixIdx; simp

omit [Fintype E] in
lemma mem_prefixSet_iff {n : ℕ} (σ : Fin n → E) (k : ℕ) (e : E) :
    e ∈ prefixSet σ k ↔ ∃ s : Fin n, (s : ℕ) < k ∧ σ s = e := by
  unfold prefixSet prefixIdx
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype E] in
lemma prefixSet_zero {n : ℕ} (σ : Fin n → E) : prefixSet σ 0 = ∅ := by
  unfold prefixSet; rw [prefixIdx_zero, Finset.image_empty]

omit [Fintype E] in
lemma prefixSet_succ_lt {n : ℕ} (σ : Fin n → E) (t : ℕ) (ht : t < n) :
    prefixSet σ (t+1) = insert (σ ⟨t, ht⟩) (prefixSet σ t) := by
  unfold prefixSet; rw [prefixIdx_succ_lt n t ht, Finset.image_insert]

omit [Fintype E] in
lemma prefixSet_succ_ge {n : ℕ} (σ : Fin n → E) (t : ℕ) (ht : n ≤ t) :
    prefixSet σ (t+1) = prefixSet σ t := by
  unfold prefixSet; rw [prefixIdx_succ_ge n t ht]


lemma prefixSet_card {n : ℕ} (σ : Fin n ≃ E) :
    prefixSet (σ : Fin n → E) n = Finset.univ := by
  unfold prefixSet prefixIdx
  apply Finset.eq_univ_of_forall
  intro e
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨σ.symm e, (σ.symm e).2, by simp⟩


lemma condNorm_insert (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E) :
    condNorm μ (insert e F) η = ∑ ω, if (Agree F η ω ∧ ω e = η e) then μ ω else 0 := by
  unfold condNorm
  apply Finset.sum_congr rfl
  intro ω _
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨fun f hf => h f (Finset.mem_insert_of_mem hf), h e (Finset.mem_insert_self e F)⟩
  · rintro ⟨hF, he⟩ f hf
    rcases Finset.mem_insert.mp hf with rfl | hf'
    · exact he
    · exact hF f hf'


lemma condProbBit_eq_ratio (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E) :
    condProbBit μ F η e (η e) = condNorm μ (insert e F) η / condNorm μ F η := by
  unfold condProbBit; rw [condNorm_insert]


lemma telescope_step (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) (e : E)
    (hF : condNorm μ F η ≠ 0) :
    condNorm μ (insert e F) η = condProbBit μ F η e (η e) * condNorm μ F η := by
  rw [condProbBit_eq_ratio]; field_simp


lemma condNorm_prefix_telescope (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    {n : ℕ} (σ : Fin n → E) (η : ConfigSpace E) (t : ℕ) :
    condNorm μ (prefixSet σ t) η
      = (∏ s ∈ prefixIdx n t, condProbBit μ (prefixSet σ (s : ℕ)) η (σ s) (η (σ s)))
        * condNorm μ (∅ : Finset E) η := by
  induction t with
  | zero =>
    rw [prefixIdx_zero, Finset.prod_empty, one_mul, prefixSet_zero]
  | succ t ih =>
    by_cases ht : t < n
    · rw [prefixIdx_succ_lt n t ht, Finset.prod_insert (mem_prefixIdx_lt n t ht),
          prefixSet_succ_lt σ t ht,
          telescope_step μ (prefixSet σ t) η (σ ⟨t, ht⟩)
            (OSSS.Monotonic.condNorm_pos hpos _ _).ne', ih]
      ring
    · have ht' : n ≤ t := not_lt.mp ht
      rw [prefixIdx_succ_ge n t ht', prefixSet_succ_ge σ t ht', ih]


lemma condNorm_empty (μ : ConfigSpace E → ℝ) (η : ConfigSpace E) :
    condNorm μ (∅ : Finset E) η = ∑ ω, μ ω := by
  unfold condNorm Agree
  apply Finset.sum_congr rfl
  intro ω _
  rw [if_pos]
  intro f hf
  exact absurd hf (Finset.notMem_empty f)


lemma condNorm_univ (μ : ConfigSpace E → ℝ) (η : ConfigSpace E) :
    condNorm μ (Finset.univ : Finset E) η = μ η := by
  unfold condNorm
  rw [Finset.sum_eq_single η]
  · rw [if_pos (agree_self _ _)]
  · intro ω _ hne
    rw [if_neg]
    intro hag
    exact hne (funext fun e => hag e (Finset.mem_univ e))
  · intro h; exact absurd (Finset.mem_univ η) h


end OSSS.Coding
end StatMech
