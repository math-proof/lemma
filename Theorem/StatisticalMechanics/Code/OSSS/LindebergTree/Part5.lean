/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LindebergTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Def.StatisticalMechanics.Code.OSSS.LindebergTree.Part5
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace LindebergTree

open OSSS.Monotonic OSSS.Coding OSSS.Lindeberg

open OSSS.DecisionTree

section Analytic

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma freshAt_eq_diff (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) (e : E) :
    freshAt T ω t e
      = (if e ∈ pathPrefix T ω (t + 1) then (1 : ℝ) else 0)
        - (if e ∈ pathPrefix T ω t then (1 : ℝ) else 0) := by
  unfold freshAt
  by_cases h1 : e ∈ pathPrefix T ω (t + 1)
  · by_cases h0 : e ∈ pathPrefix T ω t
    · rw [if_neg (by tauto), if_pos h1, if_pos h0]; ring
    · rw [if_pos ⟨h1, h0⟩, if_pos h1, if_neg h0]; ring
  · have h0 : e ∉ pathPrefix T ω t := fun hmem =>
      h1 (pathPrefix_mono T ω (Nat.le_succ t) hmem)
    rw [if_neg (by tauto), if_neg h1, if_neg h0]; ring


lemma sum_freshAt_eq_queried (T : DecisionTree E) (ω : ConfigSpace E) (e : E) :
    ∑ t ∈ Finset.range (treeDepth T), freshAt T ω t e
      = if e ∈ T.queried ω then (1 : ℝ) else 0 := by
  simp_rw [freshAt_eq_diff T ω]
  rw [Finset.sum_range_sub (fun t => if e ∈ pathPrefix T ω t then (1 : ℝ) else 0) (treeDepth T)]
  rw [pathPrefix_depth_eq_queried, pathPrefix_zero]
  simp


lemma pathPrefix_succ_eq_or_insert (T : DecisionTree E) (ω : ConfigSpace E) (t : ℕ) :
    pathPrefix T ω (t + 1) = pathPrefix T ω t ∨
      ∃ a, a ∉ pathPrefix T ω t ∧ pathPrefix T ω (t + 1) = insert a (pathPrefix T ω t) := by
  induction T generalizing t ω with
  | leaf b => left; rw [pathPrefix_leaf, pathPrefix_leaf]
  | node eN l r IHl IHr =>
    cases t with
    | zero =>
      rw [pathPrefix_node_succ, pathPrefix_zero]
      by_cases heN : eN ∈ pathPrefix (if ω eN then l else r) ω 0
      · rw [pathPrefix_zero] at heN; exact absurd heN (Finset.notMem_empty eN)
      · right; refine ⟨eN, Finset.notMem_empty eN, ?_⟩
        rw [pathPrefix_zero]
    | succ k =>
      rw [pathPrefix_node_succ, pathPrefix_node_succ]
      set br := (if ω eN then l else r) with hbr
      have IH : pathPrefix br ω (k + 1) = pathPrefix br ω k ∨
          ∃ a, a ∉ pathPrefix br ω k ∧ pathPrefix br ω (k + 1) = insert a (pathPrefix br ω k) := by
        by_cases he : ω eN
        · simp only [hbr, he, if_true]; exact IHl ω k
        · simp only [hbr, he, Bool.false_eq_true, if_false]; exact IHr ω k
      rcases IH with heq | ⟨a, hanew, ha⟩
      · left; rw [heq]
      · rw [ha]
        by_cases haeN : a = eN
        · subst haeN; left; rw [Finset.insert_comm, Finset.insert_idem]
        · by_cases heNmem : eN ∈ pathPrefix br ω k
          · 
            right; refine ⟨a, ?_, ?_⟩
            · rw [Finset.mem_insert]; rintro (rfl | hmem)
              · exact haeN rfl
              · exact hanew hmem
            · rw [Finset.insert_comm]
          · 
            
            right; refine ⟨a, ?_, ?_⟩
            · rw [Finset.mem_insert]; rintro (rfl | hmem)
              · exact haeN rfl
              · exact hanew hmem
            · rw [Finset.insert_comm]


lemma adaptM_step_eq_of_prefix_eq {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (ω : ConfigSpace E)
    (h : pathPrefix T ω (t + 1) = pathPrefix T ω t) :
    adaptM μ T f (t + 1) ω = adaptM μ T f t ω := by
  unfold adaptM; rw [h]


lemma abs_step_eq_sum_freshAt {μ : ConfigSpace E → ℝ} (T : DecisionTree E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (ω : ConfigSpace E) :
    |adaptM μ T f (t + 1) ω - adaptM μ T f t ω|
      = ∑ e, |adaptM μ T f (t + 1) ω - adaptM μ T f t ω| * freshAt T ω t e := by
  by_cases hgrow : pathPrefix T ω (t + 1) = pathPrefix T ω t
  · 
    rw [adaptM_step_eq_of_prefix_eq T f t ω hgrow]
    simp only [sub_self, abs_zero, zero_mul, Finset.sum_const_zero]
  · 
    have hsub : pathPrefix T ω t ⊆ pathPrefix T ω (t + 1) :=
      pathPrefix_mono T ω (Nat.le_succ t)
    
    have hsumfresh : (∑ e, freshAt T ω t e)
        = ((pathPrefix T ω (t + 1) \ pathPrefix T ω t).card : ℝ) := by
      unfold freshAt
      rw [Finset.sum_boole]
      congr 1
      apply Finset.card_bij (fun e _ => e)
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        exact Finset.mem_sdiff.mpr ⟨he.1, he.2⟩
      · intro a _ b _ hab; exact hab
      · intro e he
        rw [Finset.mem_sdiff] at he
        exact ⟨e, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨he.1, he.2⟩, rfl⟩
    
    have hcard1 : (pathPrefix T ω (t + 1) \ pathPrefix T ω t).card = 1 := by
      rcases pathPrefix_succ_eq_or_insert T ω t with heq | ⟨a, hanew, ha⟩
      · exact absurd heq hgrow
      · rw [ha, Finset.insert_sdiff_cancel hanew]; simp
    rw [hcard1] at hsumfresh
    rw [← Finset.mul_sum, hsumfresh]
    simp


end Analytic
end LindebergTree
end OSSS
end StatMech
