/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Coding.Part4
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma recon (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E) (hσ : Function.Injective σ)
    (x : ConfigSpace E) (u : Fin n → ℝ) (m : ℕ) (hm : m ≤ n)
    (H : ∀ (t : ℕ) (ht : t < m),
        x (σ ⟨t, by omega⟩) = decide (u ⟨t, by omega⟩ ≥ thr μ σ x ⟨t, by omega⟩)) :
    Agree (prefixSet σ m) x (codePrefix μ σ u m) := by
  induction m with
  | zero => intro f hf; simp [prefixSet, prefixIdx] at hf
  | succ m ih =>
    have hmn : m < n := by omega
    have ihA : Agree (prefixSet σ m) x (codePrefix μ σ u m) := by
      apply ih (by omega)
      intro t ht; exact H t (by omega)
    intro f hf
    rw [prefixSet_succ_lt σ m hmn] at hf
    show codePrefix μ σ u (m+1) f = x f
    conv_lhs => unfold codePrefix
    simp only [hmn, dif_pos]
    rcases Finset.mem_insert.mp hf with rfl | hfm
    · rw [Function.update_self]
      have hcong : condProbClosed μ (prefixSet σ m) (codePrefix μ σ u m) (σ ⟨m, hmn⟩)
          = thr μ σ x ⟨m, hmn⟩ := by
        unfold thr
        symm
        exact condProbClosed_congr μ (prefixSet σ m) x (codePrefix μ σ u m) (σ ⟨m, hmn⟩)
          (fun g hg => (ihA g hg).symm)
      rw [hcong]
      have hH := H m (Nat.lt_succ_self m)
      simp only at hH ⊢
      rw [hH]
    · have hne : f ≠ σ ⟨m, hmn⟩ := by
        intro h; rw [h] at hfm
        obtain ⟨s, hs, hseq⟩ := (mem_prefixSet_iff σ m _).mp hfm
        have hsm := hσ hseq
        rw [hsm] at hs; exact (lt_irrefl m) hs
      rw [Function.update_of_ne hne]
      exact ihA f hfm


lemma codeMap_eq_imp (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (x : ConfigSpace E) (u : Fin n → ℝ)
    (hx : codeMap μ σ u = x) (t : Fin n) :
    x (σ t) = decide (u t ≥ thr μ σ x t) := by
  obtain ⟨t, ht⟩ := t
  have hstep := codePrefix_succ_self μ σ u t ht
  have hval : codeMap μ σ u (σ ⟨t, ht⟩) = codePrefix μ σ u (t+1) (σ ⟨t, ht⟩) := by
    unfold codeMap
    exact codePrefix_stable μ σ hσ u (t+1) n ht (σ ⟨t, ht⟩)
      (by rw [mem_prefixSet_iff]; exact ⟨⟨t, ht⟩, Nat.lt_succ_self t, rfl⟩)
  have hagree : ∀ g ∈ prefixSet σ t, codePrefix μ σ u t g = x g := by
    intro g hg
    rw [codePrefix_agree_codeMap μ σ hσ u t (by omega) g hg, hx]
  have hcong : condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)
      = thr μ σ x ⟨t, ht⟩ := by
    unfold thr
    exact condProbClosed_congr μ (prefixSet σ t) (codePrefix μ σ u t) x (σ ⟨t, ht⟩) hagree
  calc x (σ ⟨t, ht⟩)
      = codeMap μ σ u (σ ⟨t, ht⟩) := by rw [hx]
    _ = codePrefix μ σ u (t+1) (σ ⟨t, ht⟩) := hval
    _ = decide (u ⟨t, ht⟩ ≥ condProbClosed μ (prefixSet σ t) (codePrefix μ σ u t) (σ ⟨t, ht⟩)) :=
          hstep
    _ = decide (u ⟨t, ht⟩ ≥ thr μ σ x ⟨t, ht⟩) := by rw [hcong]


lemma codeMap_eq_iff (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) (u : Fin n → ℝ) :
    codeMap μ (σ : Fin n → E) u = x
      ↔ ∀ t : Fin n, x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t) := by
  have hσ : Function.Injective (σ : Fin n → E) := σ.injective
  constructor
  · intro hx t; exact codeMap_eq_imp μ (σ : Fin n → E) hσ x u hx t
  · intro H
    have hag : Agree (prefixSet (σ : Fin n → E) n) x (codeMap μ (σ : Fin n → E) u) := by
      unfold codeMap
      exact recon μ (σ : Fin n → E) hσ x u n le_rfl (fun t ht => H ⟨t, ht⟩)
    rw [prefixSet_card σ] at hag
    funext e
    exact hag e (Finset.mem_univ e)


lemma thr_mem_Icc (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : 0 ≤ thr μ σ x t ∧ thr μ σ x t ≤ 1 := by
  have hZ : 0 < condNorm μ (prefixSet σ (t : ℕ)) x := OSSS.Monotonic.condNorm_pos hpos _ _
  unfold thr
  exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) _ x _ false hZ,
         condProbBit_le_one (fun ω => (hpos ω).le) _ x _ false hZ⟩


end OSSS.Coding
end StatMech
