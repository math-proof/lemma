/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Poincare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Def.StatisticalMechanics.Code.OSSS.Poincare
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace Poincare

open DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in


lemma eval_fullTree (φ : ConfigSpace E → Bool) (l : List E)
    (h : InsensOutside φ l) (ω : ConfigSpace E) :
    (fullTree φ l).eval ω = φ ω := by
  induction l generalizing φ with
  | nil =>
      simp only [fullTree, DecisionTree.eval]
      exact h (fun _ => false) ω (by intro e he; simp at he)
  | cons e l ih =>
      simp only [fullTree, DecisionTree.eval]
      by_cases he : ω e = true
      · rw [if_pos he]
        have hins : InsensOutside (fun ω => φ (setOpen e ω)) l := by
          intro a b hab
          apply h
          intro x hx
          rcases List.mem_cons.1 hx with h1 | h1
          · subst h1; simp [setOpen]
          · by_cases hxe : x = e
            · subst hxe; simp [setOpen]
            · rw [setOpen_of_ne hxe, setOpen_of_ne hxe]; exact hab x h1
        rw [ih _ hins]
        congr 1
        funext x
        by_cases hxe : x = e
        · subst hxe; simp [setOpen, he]
        · rw [setOpen_of_ne hxe]
      · rw [if_neg he]
        have he' : ω e = false := by cases ho : ω e; rfl; exact absurd ho he
        have hins : InsensOutside (fun ω => φ (setClosed e ω)) l := by
          intro a b hab
          apply h
          intro x hx
          rcases List.mem_cons.1 hx with h1 | h1
          · subst h1; simp [setClosed]
          · by_cases hxe : x = e
            · subst hxe; simp [setClosed]
            · rw [setClosed_of_ne hxe, setClosed_of_ne hxe]; exact hab x h1
        rw [ih _ hins]
        congr 1
        funext x
        by_cases hxe : x = e
        · subst hxe; simp [setClosed, he']
        · rw [setClosed_of_ne hxe]

omit [Fintype E] in


lemma mem_queried_fullTree (e : E) (φ : ConfigSpace E → Bool) (l : List E)
    (he : e ∈ l) (ω : ConfigSpace E) :
    e ∈ (fullTree φ l).queried ω := by
  induction l generalizing φ ω with
  | nil => exact absurd he (by simp)
  | cons a l ih =>
      simp only [fullTree, DecisionTree.queried]
      rcases List.mem_cons.1 he with h1 | h1
      · subst h1; exact Finset.mem_insert_self e _
      · apply Finset.mem_insert_of_mem
        by_cases hae : ω a = true
        · rw [if_pos hae]; exact ih (fun ω => φ (setOpen a ω)) h1 ω
        · rw [if_neg hae]; exact ih (fun ω => φ (setClosed a ω)) h1 ω


end Poincare
end OSSS
end StatMech
