/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree.Part2
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Path

variable {E : Type*} [DecidableEq E]


lemma queried_leaf (b : Bool) (ω : ConfigSpace E) :
    (DecisionTree.queried (leaf b) ω) = (∅ : Finset E) := rfl

lemma queried_node (e : E) (l r : DecisionTree E) (ω : ConfigSpace E) :
    DecisionTree.queried (node e l r) ω
      = insert e (if ω e then l.queried ω else r.queried ω) := rfl


lemma pathPrefix_subset_queried (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix T ω t ⊆ T.queried ω := by
  induction T generalizing t with
  | leaf b => rw [pathPrefix_leaf, queried_leaf]
  | node e l r IHl IHr =>
    cases t with
    | zero => rw [pathPrefix_zero]; exact Finset.empty_subset _
    | succ k =>
      rw [pathPrefix_node_succ, queried_node]
      apply Finset.insert_subset_insert
      by_cases he : ω e
      · simp only [he, if_true]; exact IHl k
      · simp only [he, Bool.false_eq_true, if_false]; exact IHr k


lemma pathPrefix_mono (T : DecisionTree E) (ω : ConfigSpace E) {s t : ℕ} (hst : s ≤ t) :
    pathPrefix T ω s ⊆ pathPrefix T ω t := by
  induction T generalizing s t with
  | leaf b => rw [pathPrefix_leaf, pathPrefix_leaf]
  | node e l r IHl IHr =>
    cases s with
    | zero => rw [pathPrefix_zero]; exact Finset.empty_subset _
    | succ k =>
      cases t with
      | zero => omega
      | succ m =>
        rw [pathPrefix_node_succ, pathPrefix_node_succ]
        apply Finset.insert_subset_insert
        by_cases he : ω e
        · simp only [he, if_true]; exact IHl (by omega)
        · simp only [he, Bool.false_eq_true, if_false]; exact IHr (by omega)


lemma pathPrefix_ge_depth (T : DecisionTree E) (ω : ConfigSpace E) {s : ℕ}
    (hs : treeDepth T ≤ s) :
    pathPrefix T ω s = T.queried ω := by
  induction T generalizing ω s with
  | leaf b => rw [pathPrefix_leaf, queried_leaf]
  | node e l r IHl IHr =>
    rw [treeDepth] at hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    rw [pathPrefix_node_succ, queried_node]
    congr 1
    by_cases he : ω e
    · simp only [he, if_true]
      exact IHl ω (by omega)
    · simp only [he, Bool.false_eq_true, if_false]
      exact IHr ω (by omega)


lemma pathPrefix_depth_eq_queried (T : DecisionTree E) (ω : ConfigSpace E) :
    pathPrefix T ω (treeDepth T) = T.queried ω :=
  pathPrefix_ge_depth T ω le_rfl

end Path
end LindebergTree
end OSSS
end StatMech
