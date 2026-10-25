/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCouplingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.LindebergTree.Part6
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCouplingAssembly

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma codePrefix_congr_of_agree (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (m : ℕ) (hm : m ≤ n)
    (h : ∀ i : Fin n, (i : ℕ) < m → u i = u' i) :
    codePrefix μ σ u m = codePrefix μ σ u' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hmn : m < n := by omega
    have iheq : codePrefix μ σ u m = codePrefix μ σ u' m :=
      ih (by omega) (fun i hi => h i (by omega))
    conv_lhs => unfold codePrefix
    conv_rhs => unfold codePrefix
    simp only [hmn, dif_pos]
    rw [iheq, h ⟨m, hmn⟩ (Nat.lt_succ_self m)]


lemma codePrefix_step_congr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (m : ℕ) (hmn : m < n)
    (hpre : codePrefix μ σ u m = codePrefix μ σ u' m)
    (hum : u ⟨m, hmn⟩ = u' ⟨m, hmn⟩) :
    codePrefix μ σ u (m+1) = codePrefix μ σ u' (m+1) := by
  conv_lhs => unfold codePrefix
  conv_rhs => unfold codePrefix
  simp only [hmn, dif_pos]
  rw [hpre, hum]


lemma codePrefix_forward (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (start : ℕ)
    (hagree : ∀ i : Fin n, start ≤ (i : ℕ) → u i = u' i)
    (hstart : codePrefix μ σ u start = codePrefix μ σ u' start) :
    ∀ m, start ≤ m → m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
  intro m hsm hm
  obtain ⟨d, rfl⟩ : ∃ d, m = start + d := ⟨m - start, by omega⟩
  clear hsm
  induction d with
  | zero => simpa using hstart
  | succ d ih =>
    have hmn : start + d < n := by omega
    have hpre := ih (by omega)
    have hum : u ⟨start+d, hmn⟩ = u' ⟨start+d, hmn⟩ :=
      hagree ⟨start+d, hmn⟩ (Nat.le_add_right start d)
    have := codePrefix_step_congr μ σ u u' (start+d) hmn hpre hum
    convert this using 2


lemma codePrefix_det (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (u u' : Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
    (hbit : codePrefix μ σ u (k+1) (σ ⟨k, hk⟩) = codePrefix μ σ u' (k+1) (σ ⟨k, hk⟩)) :
    ∀ m, m ≤ n → codePrefix μ σ u m = codePrefix μ σ u' m := by
  have hk_agree : codePrefix μ σ u k = codePrefix μ σ u' k :=
    codePrefix_congr_of_agree μ σ u u' k (by omega) (fun i hi => hagree i (by omega))
  have hk1_agree : codePrefix μ σ u (k+1) = codePrefix μ σ u' (k+1) := by
    funext e
    by_cases he : e = σ ⟨k, hk⟩
    · subst he; exact hbit
    · conv_lhs => unfold codePrefix
      conv_rhs => unfold codePrefix
      simp only [hk, dif_pos]
      rw [Function.update_of_ne he, Function.update_of_ne he, hk_agree]
  intro m hm
  rcases le_or_gt m k with hmk | hmk
  · exact codePrefix_congr_of_agree μ σ u u' m hm (fun i hi => hagree i (by omega))
  · exact codePrefix_forward μ σ u u' (k+1) (fun i hi => hagree i (by omega)) hk1_agree m hmk hm


lemma codeMap_det (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (hσ : Function.Injective σ) (u u' : Fin n → ℝ) (k : ℕ) (hk : k < n)
    (hagree : ∀ i : Fin n, (i : ℕ) ≠ k → u i = u' i)
    (hbit : codeMap μ σ u (σ ⟨k, hk⟩) = codeMap μ σ u' (σ ⟨k, hk⟩)) :
    codeMap μ σ u = codeMap μ σ u' := by
  
  have hval : ∀ v : Fin n → ℝ,
      codeMap μ σ v (σ ⟨k, hk⟩) = codePrefix μ σ v (k+1) (σ ⟨k, hk⟩) := by
    intro v
    unfold codeMap
    exact codePrefix_stable μ σ hσ v (k+1) n hk (σ ⟨k, hk⟩)
      (by rw [mem_prefixSet_iff]; exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩)
  have hbit' : codePrefix μ σ u (k+1) (σ ⟨k, hk⟩) = codePrefix μ σ u' (k+1) (σ ⟨k, hk⟩) := by
    rw [← hval u, ← hval u', hbit]
  have := codePrefix_det μ σ u u' k hk hagree hbit' n le_rfl
  unfold codeMap
  exact this


lemma Wt_agree_off {n : ℕ} (U V : Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∀ i : Fin n, (i : ℕ) ≠ t - 1 → Wt U V t i = Wt U V (t-1) i := by
  intro i hi
  unfold Wt
  by_cases h : (i:ℕ) < t
  · have h' : (i:ℕ) < t - 1 := by omega
    simp [h, h']
  · have h' : ¬ (i:ℕ) < t - 1 := by omega
    simp [h, h']


lemma Wt_at_pos {n : ℕ} (U V : Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) :
    Wt U V t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ Wt U V (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
  unfold Wt
  refine ⟨?_, ?_⟩
  · have h : (⟨t-1, htn⟩ : Fin n).val < t := by show t - 1 < t; omega
    simp [h]
  · have h : ¬ (⟨t-1, htn⟩ : Fin n).val < t - 1 := by show ¬ t - 1 < t - 1; exact lt_irrefl _
    simp only [h, if_false]


end GrandCouplingAssembly
end OSSS
end StatMech
