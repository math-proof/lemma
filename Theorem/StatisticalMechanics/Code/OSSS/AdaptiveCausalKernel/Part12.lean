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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part12
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


lemma sharedStepIndicator_nonneg (T : DecisionTree E)
    (base : ConfigSpace E) (t : ℕ) (e : E) :
    0 ≤ sharedStepIndicator T base t e := by
  have hsub := sharedEdges_extendDecisionTreeAt_succ_subset
    t T base base (Finset.univ : Finset E) (by simp)
  unfold sharedStepIndicator sharedAtIndicator
  by_cases hnext : e ∈ sharedEdges
      (extendDecisionTreeAt (t + 1) T base (Finset.univ : Finset E)) base
  · have hnow := hsub hnext
    simp [hnext, hnow]
  · simp [hnext]
    split <;> norm_num


theorem sum_sharedStepIndicator_eq_queried (T : DecisionTree E)
    (base : ConfigSpace E) (e : E) :
    ∑ t ∈ Finset.range (Fintype.card E), sharedStepIndicator T base t e =
      if e ∈ T.queried base then 1 else 0 := by
  unfold sharedStepIndicator
  rw [Finset.sum_range_sub' (fun t => sharedAtIndicator T base t e)
    (Fintype.card E)]
  unfold sharedAtIndicator
  rw [extendDecisionTreeAt_zero, sharedEdges_extendDecisionTree_univ]
  rw [sharedEdges_extendDecisionTreeAt_card_univ]
  simp


theorem sum_mean_sharedStepIndicator_eq_revealmentMu
    (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (e : E) :
    ∑ t ∈ Finset.range (Fintype.card E),
        Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) =
      LindebergTree.revealmentMu μ T e := by
  unfold Lindeberg.mean LindebergTree.revealmentMu
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro base _
  rw [← Finset.sum_mul]
  rw [sum_sharedStepIndicator_eq_queried]

lemma sharedEdges_subset {R : Finset E} (S : CausalOrder R)
    (base : ConfigSpace E) : sharedEdges S base ⊆ R := by
  induction S with
  | done => simp [sharedEdges]
  | @node R q hq active closed opened ihc iho =>
      by_cases hb : base q <;> by_cases ha : active
      · simpa [sharedEdges, hb, ha] using iho.trans (Finset.erase_subset q R)
      · simp [sharedEdges, hb, ha, Finset.insert_subset_iff, hq,
          iho.trans (Finset.erase_subset q R)]
      · simpa [sharedEdges, hb, ha] using ihc.trans (Finset.erase_subset q R)
      · simp [sharedEdges, hb, ha, Finset.insert_subset_iff, hq,
          ihc.trans (Finset.erase_subset q R)]

lemma mem_sharedEdges_iff_independentAt_false {R : Finset E}
    (S : CausalOrder R) (base : ConfigSpace E) (e : E) (he : e ∈ R) :
    e ∈ sharedEdges S base ↔ independentAt S base e = false := by
  induction S with
  | done => simp at he
  | @node R q hq active closed opened ihc iho =>
      by_cases heq : e = q
      · subst e
        have hno : q ∉ sharedEdges opened base := by
          intro h
          exact (Finset.mem_erase.mp (sharedEdges_subset opened base h)).1 rfl
        have hnc : q ∉ sharedEdges closed base := by
          intro h
          exact (Finset.mem_erase.mp (sharedEdges_subset closed base h)).1 rfl
        by_cases hb : base q <;> by_cases ha : active <;>
          simp [sharedEdges, independentAt, hb, ha, hno, hnc]
      · have heErase : e ∈ R.erase q := Finset.mem_erase.mpr ⟨heq, he⟩
        by_cases hb : base q
        · by_cases ha : active <;>
            simp [sharedEdges, independentAt, heq, hb, ha, iho heErase]
        · by_cases ha : active <;>
            simp [sharedEdges, independentAt, heq, hb, ha, ihc heErase]

end AdaptiveCausalKernel
end OSSS
end StatMech
