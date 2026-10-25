/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
import Def.StatisticalMechanics.Code.OSSS.RevealmentCrossBox
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

theorem fst_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    (xbStep endU endV o s e b).1 = geomStep endU endV s.1 e b := by
  unfold xbStep geomStep
  by_cases hb : b
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

omit [Fintype E] [DecidableEq E] in


theorem snd_xbStep_eq (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    (xbStep endU endV o s e b).2 =
      (if o ∈ geomStep endU endV s.1 e b then insert o else id)
        (if b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
          then insert (endU e) (insert (endV e) s.2) else s.2) := by
  conv_lhs => unfold xbStep
  simp only
  rw [show (if b then insert (endU e) (insert (endV e) s.1) else s.1)
      = geomStep endU endV s.1 e b from by unfold geomStep; rfl]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho, if_pos ho]
  · rw [if_neg ho, if_neg ho]; rfl


omit [Fintype E] [DecidableEq E] in


theorem fst_runState_xbStep (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1
      = runState (geomGuard endU endV) (geomStep endU endV) ω l s.1 := by
  induction l generalizing s with
  | nil => rfl
  | cons e rest ih =>
      simp only [runState]
      have hguard : xbGuard endU endV s e = geomGuard endU endV s.1 e := rfl
      rw [hguard]
      by_cases hg : geomGuard endU endV s.1 e = true
      · rw [if_pos hg, if_pos hg, ih, fst_xbStep]
      · rw [if_neg hg, if_neg hg, ih]


omit [Fintype E] [DecidableEq E] in

theorem subset_snd_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    s.2 ⊆ (xbStep endU endV o s e b).2 := by
  rw [snd_xbStep_eq]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho]
    refine subset_trans ?_ (Finset.subset_insert _ _)
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
    · rw [if_neg hc]
  · rw [if_neg ho]; simp only [id]
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
    · rw [if_neg hc]

omit [Fintype E] [DecidableEq E] in

theorem subset_snd_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    s.2 ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
  induction l generalizing s with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact subset_trans (subset_snd_xbStep endU endV o s e (ω e)) (ih _)
      · rw [if_neg hg]; exact ih _

omit [Fintype E] [DecidableEq E] in

theorem snd_sub_fst_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool)
    (hs : s.2 ⊆ s.1) :
    (xbStep endU endV o s e b).2 ⊆ (xbStep endU endV o s e b).1 := by
  rw [snd_xbStep_eq, fst_xbStep]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho]
    apply Finset.insert_subset ho
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; unfold geomStep; rw [if_pos hc.1]
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)
    · rw [if_neg hc]; exact subset_trans hs (subset_geomStep endU endV s.1 e b)
  · rw [if_neg ho]; simp only [id]
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; unfold geomStep; rw [if_pos hc.1]
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)
    · rw [if_neg hc]; exact subset_trans hs (subset_geomStep endU endV s.1 e b)

omit [Fintype E] [DecidableEq E] in

theorem snd_sub_fst_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1 := by
  induction l generalizing s with
  | nil => simpa [runState] using hs
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (snd_sub_fst_xbStep endU endV o s e (ω e) hs)
      · rw [if_neg hg]; exact ih s hs


end OSSS
end StatMech
