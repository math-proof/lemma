/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part10
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


@[simp] lemma sharedEdges_allIndependent {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges (allIndependent S) base = ∅ := by
  induction S with
  | done => rfl
  | node e he independent closed opened ihc iho =>
      simp only [allIndependent, sharedEdges, if_true]
      split <;> assumption

lemma allIndependent_cast {R S : Finset E} (h : R = S) (C : CausalOrder R) :
    allIndependent (h ▸ C) = h ▸ allIndependent C := by
  subst S
  rfl

@[simp] lemma allIndependent_fixedListOrder (l : List E) (h : l.Nodup) :
    allIndependent (fixedListOrder l h) = fixedListOrder l h := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rw [fixedListOrder, allIndependent]
      congr 1
      all_goals
        rw [allIndependent_cast]
        simpa using ih (List.nodup_cons.mp h).2

@[simp] lemma allIndependent_fixedOrder (R : Finset E) :
    allIndependent (fixedOrder R) = fixedOrder R := by
  unfold fixedOrder
  rw [allIndependent_cast, allIndependent_fixedListOrder]

lemma sharedEdges_cast {R S : Finset E} (h : R = S) (C : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges (h ▸ C) base = sharedEdges C base := by
  subst S
  rfl

lemma sharedEdges_fixedListOrder (l : List E) (h : l.Nodup) (base : ConfigSpace E) :
    sharedEdges (fixedListOrder l h) base = ∅ := by
  induction l with
  | nil => simp [fixedListOrder, sharedEdges]
  | cons e l ih =>
      rw [fixedListOrder]
      simp only [sharedEdges, if_true]
      split
      · rw [sharedEdges_cast]
        exact ih _
      · rw [sharedEdges_cast]
        exact ih _

@[simp] lemma sharedEdges_fixedOrder (R : Finset E) (base : ConfigSpace E) :
    sharedEdges (fixedOrder R) base = ∅ := by
  let C := fixedListOrder R.toList R.nodup_toList
  let h : R.toList.toFinset = R := Finset.toList_toFinset R
  have hfixed : fixedOrder R = h ▸ C := by
    unfold fixedOrder
    rfl
  rw [hfixed, sharedEdges_cast h C base]
  exact sharedEdges_fixedListOrder R.toList R.nodup_toList base


theorem sharedEdges_extendDecisionTree (T : DecisionTree E) (known base : ConfigSpace E)
    (R : Finset E) (hknown : ∀ z, z ∉ R → known z = base z) :
    sharedEdges (extendDecisionTree T known R) base = T.queried base ∩ R := by
  induction T generalizing known R with
  | leaf b => simp [extendDecisionTree, DecisionTree.queried]
  | node e opened closed iho ihc =>
      rw [extendDecisionTree]
      by_cases he : e ∈ R
      · rw [dif_pos he]
        by_cases hb : base e
        · simp only [sharedEdges, hb, if_true, Bool.false_eq_true, if_false,
            DecisionTree.queried]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e true z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb]
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          rw [iho (Function.update known e true) (R.erase e) hk]
          ext z
          simp only [Finset.mem_insert, Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hz, _, hzR⟩)
            · exact ⟨Or.inl rfl, he⟩
            · exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · exact Or.inl hz
            · by_cases hze : z = e
              · exact Or.inl hze
              · exact Or.inr ⟨hz, hze, hzR⟩
        · have hb' : base e = false := Bool.eq_false_of_not_eq_true hb
          simp only [sharedEdges, hb, Bool.false_eq_true, if_false,
            DecisionTree.queried]
          have hk : ∀ z, z ∉ R.erase e →
              Function.update known e false z = base z := by
            intro z hz
            by_cases hze : z = e
            · subst z
              simp [hb']
            · rw [Function.update_of_ne hze]
              apply hknown z
              intro hzR
              exact hz (Finset.mem_erase.mpr ⟨hze, hzR⟩)
          rw [ihc (Function.update known e false) (R.erase e) hk]
          ext z
          simp only [Finset.mem_insert, Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hz, _, hzR⟩)
            · exact ⟨Or.inl rfl, he⟩
            · exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · exact Or.inl hz
            · by_cases hze : z = e
              · exact Or.inl hze
              · exact Or.inr ⟨hz, hze, hzR⟩
      · rw [dif_neg he]
        have hkb : known e = base e := hknown e he
        by_cases hb : base e
        · simp only [hkb, hb, if_true, DecisionTree.queried]
          rw [iho known R hknown]
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hz, hzR⟩
            exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · subst z
              exact (he hzR).elim
            · exact ⟨hz, hzR⟩
        · simp only [hkb, hb, Bool.false_eq_true, if_false, DecisionTree.queried]
          rw [ihc known R hknown]
          ext z
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨hz, hzR⟩
            exact ⟨Or.inr hz, hzR⟩
          · rintro ⟨hz | hz, hzR⟩
            · subst z
              exact (he hzR).elim
            · exact ⟨hz, hzR⟩

theorem sharedEdges_extendDecisionTree_univ (T : DecisionTree E)
    (base : ConfigSpace E) :
    sharedEdges (extendDecisionTree T base (Finset.univ : Finset E)) base =
      T.queried base := by
  rw [sharedEdges_extendDecisionTree T base base Finset.univ (by simp)]
  simp


theorem mean_mem_sharedEdges_extendDecisionTree (μ : ConfigSpace E → ℝ)
    (T : DecisionTree E) (e : E) :
    Lindeberg.mean μ (fun base =>
      if e ∈ sharedEdges
        (extendDecisionTree T base (Finset.univ : Finset E)) base then (1 : ℝ) else 0) =
      LindebergTree.revealmentMu μ T e := by
  unfold LindebergTree.revealmentMu
  apply Finset.sum_congr rfl
  intro base _
  change (if e ∈ sharedEdges
      (extendDecisionTree T base (Finset.univ : Finset E)) base then (1 : ℝ) else 0) *
      μ base = (if e ∈ T.queried base then (1 : ℝ) else 0) * μ base
  rw [sharedEdges_extendDecisionTree_univ]


end AdaptiveCausalKernel
end OSSS
end StatMech
