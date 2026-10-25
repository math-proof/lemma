/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace TreeComplete

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {V : Type*} [DecidableEq V]

omit [Fintype E] [DecidableEq E] in

theorem subset_runState (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) :
    disc ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
  induction l generalizing disc with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg]
        refine subset_trans ?_ (ih (geomStep endU endV disc e (ω e)))
        unfold geomStep
        by_cases hb : ω e = true
        · rw [if_pos hb]
          exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
        · simp only [Bool.not_eq_true] at hb; rw [hb]; simp
      · rw [if_neg hg]; exact ih disc

omit [Fintype E] [DecidableEq E] in

theorem subset_geomStep (endU endV : E → V) (disc : Finset V) (e : E) (b : Bool) :
    disc ⊆ geomStep endU endV disc e b := by
  unfold geomStep
  cases b with
  | false => simp
  | true => exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)

omit [Fintype E] [DecidableEq E] in

theorem runState_mono (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) {d₁ d₂ : Finset V} (h : d₁ ⊆ d₂) :
    runState (geomGuard endU endV) (geomStep endU endV) ω l d₁
      ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l d₂ := by
  induction l generalizing d₁ d₂ with
  | nil => simpa [runState] using h
  | cons e rest ih =>
      simp only [runState]
      have hguardmono : geomGuard endU endV d₁ e = true → geomGuard endU endV d₂ e = true := by
        unfold geomGuard
        simp only [decide_eq_true_eq]
        rintro (hU | hV)
        · exact Or.inl (h hU)
        · exact Or.inr (h hV)
      by_cases hg1 : geomGuard endU endV d₁ e = true
      · rw [if_pos hg1, if_pos (hguardmono hg1)]
        apply ih
        unfold geomStep
        by_cases hb : ω e = true
        · rw [if_pos hb, if_pos hb]
          exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ h)
        · simp only [Bool.not_eq_true] at hb; rw [hb]; simpa using h
      · rw [if_neg hg1]
        by_cases hg2 : geomGuard endU endV d₂ e = true
        · rw [if_pos hg2]
          exact ih (subset_trans h (subset_geomStep endU endV d₂ e (ω e)))
        · rw [if_neg hg2]; exact ih h

omit [Fintype E] [DecidableEq E] in


theorem mem_runState_of_open_edge (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) (e : E) (he : e ∈ l) (hopen : ω e = true)
    (hend : endU e ∈ disc ∨ endV e ∈ disc) :
    endU e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc
      ∧ endV e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
  induction l generalizing disc with
  | nil => simp at he
  | cons f rest ih =>
      simp only [runState]
      rcases List.mem_cons.mp he with rfl | hmem
      · 
        have hg : geomGuard endU endV disc e = true := by
          unfold geomGuard; simp only [decide_eq_true_eq]; exact hend
        rw [if_pos hg]
        have hstep : geomStep endU endV disc e (ω e) = insert (endU e) (insert (endV e) disc) := by
          unfold geomStep; rw [hopen, if_pos rfl]
        rw [hstep]
        have hsub := subset_runState endU endV ω rest (insert (endU e) (insert (endV e) disc))
        exact ⟨hsub (Finset.mem_insert_self _ _),
               hsub (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
      · 
        by_cases hg : geomGuard endU endV disc f = true
        · rw [if_pos hg]
          refine ih (geomStep endU endV disc f (ω f)) hmem ?_
          have hsub := subset_geomStep endU endV disc f (ω f)
          rcases hend with hU | hV
          · exact Or.inl (hsub hU)
          · exact Or.inr (hsub hV)
        · rw [if_neg hg]; exact ih disc hmem hend


end TreeComplete
end OSSS
end StatMech
