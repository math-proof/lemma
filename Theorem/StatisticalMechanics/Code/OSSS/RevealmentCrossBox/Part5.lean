/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part4
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

theorem runState_append_xb (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l₁ l₂ : List E) (s : XState V) :
    runState (xbGuard endU endV) (xbStep endU endV o) ω (l₁ ++ l₂) s
      = runState (xbGuard endU endV) (xbStep endU endV o) ω l₂
          (runState (xbGuard endU endV) (xbStep endU endV o) ω l₁ s) := by
  induction l₁ generalizing s with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [List.cons_append, runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg, if_pos hg]; exact ih _
      · rw [if_neg hg, if_neg hg]; exact ih _

omit [Fintype E] [DecidableEq E] in

theorem runState_repeatList_xb (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (n : ℕ) (s : XState V) :
    runState (xbGuard endU endV) (xbStep endU endV o) ω (repeatList l n) s
      = (xbPass endU endV o ω l)^[n] s := by
  induction n generalizing s with
  | zero => simp [repeatList, runState]
  | succ k ih =>
      rw [repeatList, runState_append_xb, Function.iterate_succ, Function.comp_apply]
      exact ih _

omit [Fintype E] in

theorem snd_runState_subset (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ⊆ s.2 ∪ endpointsFinset endU endV l ∪ {o} := by
  induction l generalizing s with
  | nil => intro x hx; simp only [runState] at hx; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]
        refine subset_trans (ih (xbStep endU endV o s e (ω e))) ?_
        intro x hx
        
        rw [Finset.mem_union, Finset.mem_union] at hx
        rcases hx with (hstep | hrest) | hocase
        · 
          rw [snd_xbStep_eq] at hstep
          by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
          · rw [if_pos ho] at hstep
            rw [Finset.mem_insert] at hstep
            rcases hstep with rfl | hstep
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · 
              by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
              · rw [if_pos hc] at hstep
                rw [Finset.mem_insert, Finset.mem_insert] at hstep
                rcases hstep with rfl | rfl | hd
                · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                  unfold endpointsFinset
                  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
                · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                  unfold endpointsFinset
                  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
              · rw [if_neg hc] at hstep
                exact Finset.mem_union_left _ (Finset.mem_union_left _ hstep)
          · rw [if_neg ho] at hstep; simp only [id] at hstep
            by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
            · rw [if_pos hc] at hstep
              rw [Finset.mem_insert, Finset.mem_insert] at hstep
              rcases hstep with rfl | rfl | hd
              · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                unfold endpointsFinset
                exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
              · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                unfold endpointsFinset
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
            · rw [if_neg hc] at hstep
              exact Finset.mem_union_left _ (Finset.mem_union_left _ hstep)
        · 
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
        · exact Finset.mem_union_right _ hocase
      · rw [if_neg hg]
        refine subset_trans (ih s) ?_
        intro x hx
        rw [Finset.mem_union, Finset.mem_union] at hx
        rcases hx with (hd | hrest) | hocase
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
        · exact Finset.mem_union_right _ hocase


end OSSS
end StatMech
