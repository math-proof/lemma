/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.OSSS.RevealmentConstruction.Part7
import Def.StatisticalMechanics.Code.OSSS.TreeComplete
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

omit [Fintype E] in

theorem runState_subset_union (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω l disc
      ⊆ disc ∪ endpointsFinset endU endV l := by
  induction l generalizing disc with
  | nil => simp only [runState]; exact Finset.subset_union_left
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg]
        refine subset_trans (ih (geomStep endU endV disc e (ω e))) ?_
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hstep | hrest
        · 
          unfold geomStep at hstep
          by_cases hb : ω e = true
          · rw [if_pos hb] at hstep
            rw [Finset.mem_insert, Finset.mem_insert] at hstep
            rcases hstep with rfl | rfl | hd
            · refine Finset.mem_union_right _ ?_
              unfold endpointsFinset
              exact Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨e, by simp [List.mem_toFinset], rfl⟩)
            · refine Finset.mem_union_right _ ?_
              unfold endpointsFinset
              exact Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨e, by simp [List.mem_toFinset], rfl⟩)
            · exact Finset.mem_union_left _ hd
          · simp only [Bool.not_eq_true] at hb; rw [hb, if_neg (by decide)] at hstep
            exact Finset.mem_union_left _ hstep
        · 
          refine Finset.mem_union_right _ ?_
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by
              rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by
              rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
      · rw [if_neg hg]
        refine subset_trans (ih disc) ?_
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hd | hrest
        · exact Finset.mem_union_left _ hd
        · refine Finset.mem_union_right _ ?_
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by
              rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by
              rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)


end TreeComplete
end OSSS
end StatMech
