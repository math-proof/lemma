/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part3
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.TreeComplete

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]


omit [Fintype E] [DecidableEq E] in

theorem oSeedInv_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    oSeedInv o (xbStep endU endV o s e b) := by
  intro ho
  rw [snd_xbStep_eq]
  rw [fst_xbStep] at ho
  rw [if_pos ho]
  exact Finset.mem_insert_self _ _

omit [Fintype E] [DecidableEq E] in

theorem oSeedInv_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : oSeedInv o s) :
    oSeedInv o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
  induction l generalizing s with
  | nil => simpa [runState] using hs
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (oSeedInv_xbStep endU endV o s e (ω e))
      · rw [if_neg hg]; exact ih s hs


omit [Fintype E] [DecidableEq E] in


theorem mem_snd_runState_of_open_edge (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1) (e : E) (he : e ∈ l) (hopen : ω e = true)
    (hend : endU e ∈ s.2 ∨ endV e ∈ s.2) :
    endU e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ∧ endV e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
  induction l generalizing s with
  | nil => simp at he
  | cons f rest ih =>
      simp only [runState]
      rcases List.mem_cons.mp he with rfl | hmem
      · have hg : xbGuard endU endV s e = true := by
          unfold xbGuard; simp only [decide_eq_true_eq]
          rcases hend with hU | hV
          · exact Or.inl (hs hU)
          · exact Or.inr (hs hV)
        rw [if_pos hg]
        have hboth : endU e ∈ (xbStep endU endV o s e (ω e)).2
            ∧ endV e ∈ (xbStep endU endV o s e (ω e)).2 := by
          rw [snd_xbStep_eq]
          have hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2) := ⟨hopen, hend⟩
          by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
          · rw [if_pos ho, if_pos hc]
            exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                   Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
          · rw [if_neg ho]; simp only [id]; rw [if_pos hc]
            exact ⟨Finset.mem_insert_self _ _,
                   Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
        have hsub := subset_snd_runState endU endV o ω rest (xbStep endU endV o s e (ω e))
        exact ⟨hsub hboth.1, hsub hboth.2⟩
      · by_cases hg : xbGuard endU endV s f = true
        · rw [if_pos hg]
          refine ih (xbStep endU endV o s f (ω f))
            (snd_sub_fst_xbStep endU endV o s f (ω f) hs) hmem ?_
          have hsub := subset_snd_xbStep endU endV o s f (ω f)
          rcases hend with hU | hV
          · exact Or.inl (hsub hU)
          · exact Or.inr (hsub hV)
        · rw [if_neg hg]; exact ih s hs hmem hend

omit [Fintype E] [DecidableEq E] in


theorem snd_saturated_of_fixpoint (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1)
    (hfix : runState (xbGuard endU endV) (xbStep endU endV o) ω l s = s) :
    Saturated endU endV ω l s.2 := by
  intro e he hopen hend
  have h := mem_snd_runState_of_open_edge endU endV o ω l s hs e he hopen hend
  rw [hfix] at h
  exact h


omit [Fintype E] [DecidableEq E] [DecidableEq V] in


theorem pairFixpoint_iterate {W : Type*} [DecidableEq W]
    (f : (Finset W × Finset W) → (Finset W × Finset W)) (U : Finset W)
    (hinfl1 : ∀ s, s.1 ⊆ (f s).1) (hinfl2 : ∀ s, s.2 ⊆ (f s).2)
    (hb1 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).1 ⊆ U)
    (hb2 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).2 ⊆ U)
    (s₀ : Finset W × Finset W) (h01 : s₀.1 ⊆ U) (h02 : s₀.2 ⊆ U) :
    f (f^[2 * U.card] s₀) = f^[2 * U.card] s₀ := by
  set m : (Finset W × Finset W) → ℕ := fun s => s.1.card + s.2.card with hm
  have hbound : ∀ n, (f^[n] s₀).1 ⊆ U ∧ (f^[n] s₀).2 ⊆ U := by
    intro n; induction n with
    | zero => simpa using ⟨h01, h02⟩
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply]
        exact ⟨hb1 _ ih.1 ih.2, hb2 _ ih.1 ih.2⟩
  have hmle : ∀ n, m (f^[n] s₀) ≤ 2 * U.card := by
    intro n; have h := hbound n
    have h1 := Finset.card_le_card h.1
    have h2 := Finset.card_le_card h.2
    simp only [hm]; omega
  have hminfl : ∀ s, m s ≤ m (f s) := by
    intro s
    have h1 := Finset.card_le_card (hinfl1 s)
    have h2 := Finset.card_le_card (hinfl2 s)
    simp only [hm]; omega
  have hfix_of_m : ∀ s, m (f s) ≤ m s → f s = s := by
    intro s hle
    have h1 := hinfl1 s
    have h2 := hinfl2 s
    have hc1 := Finset.card_le_card h1
    have hc2 := Finset.card_le_card h2
    have hcards : (f s).1.card = s.1.card ∧ (f s).2.card = s.2.card := by
      simp only [hm] at hle; omega
    have e1 : (f s).1 = s.1 := (Finset.eq_of_subset_of_card_le h1 (le_of_eq hcards.1)).symm
    have e2 : (f s).2 = s.2 := (Finset.eq_of_subset_of_card_le h2 (le_of_eq hcards.2)).symm
    exact Prod.ext e1 e2
  have habsorb : ∀ k j, f (f^[k] s₀) = f^[k] s₀ → f^[k + j] s₀ = f^[k] s₀ := by
    intro k j hk; induction j with
    | zero => rfl
    | succ i ih =>
        have hstep : f^[k + (i + 1)] s₀ = f (f^[k + i] s₀) := by
          rw [show k + (i + 1) = (k + i) + 1 from by ring, Function.iterate_succ',
            Function.comp_apply]
        rw [hstep, ih, hk]
  by_contra hcon
  have hnofix : ∀ k, k ≤ 2 * U.card → f (f^[k] s₀) ≠ f^[k] s₀ := by
    intro k hk hfk; apply hcon
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj, habsorb k j hfk, hfk]
  have hstrict : ∀ k, k < 2 * U.card → m (f^[k] s₀) < m (f^[k + 1] s₀) := by
    intro k hk
    have hne := hnofix k (le_of_lt hk)
    have heq : f^[k + 1] s₀ = f (f^[k] s₀) := by rw [Function.iterate_succ', Function.comp_apply]
    rw [heq]
    rcases lt_or_eq_of_le (hminfl (f^[k] s₀)) with h | h
    · exact h
    · exact absurd (hfix_of_m _ (le_of_eq h.symm)) hne
  have hge : ∀ k, k ≤ 2 * U.card → k ≤ m (f^[k] s₀) := by
    intro k hk; induction k with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        exact Nat.lt_of_le_of_lt (ih (le_of_lt (Nat.lt_of_succ_le hk)))
          (hstrict j (Nat.lt_of_succ_le hk))
  have hne := hnofix (2 * U.card) le_rfl
  have heq : f^[2 * U.card + 1] s₀ = f (f^[2 * U.card] s₀) := by
    rw [Function.iterate_succ', Function.comp_apply]
  have hstr : m (f^[2 * U.card] s₀) < m (f^[2 * U.card + 1] s₀) := by
    rw [heq]
    rcases lt_or_eq_of_le (hminfl (f^[2 * U.card] s₀)) with h | h
    · exact h
    · exact absurd (hfix_of_m _ (le_of_eq h.symm)) hne
  have h1 : 2 * U.card ≤ m (f^[2 * U.card] s₀) := hge _ le_rfl
  have hle : m (f^[2 * U.card + 1] s₀) ≤ 2 * U.card := hmle _
  omega


end OSSS
end StatMech
