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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part31
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


theorem causalPairEnergy_zero (μ : ConfigSpace E → ℝ) (T : DecisionTree E) :
    causalPairEnergy μ T 0 = 0 := by
  unfold causalPairEnergy
  apply Finset.sum_eq_zero
  intro base _
  apply Finset.sum_eq_zero
  intro target _
  rw [extendDecisionTreeAt_zero]
  by_cases hj : jointProb μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = 0
  · rw [hj, mul_zero]
  · have hjAt : jointProb μ ∅ base target
        (extendDecisionTreeAt 0 T base (Finset.univ : Finset E)) ≠ 0 := by
        simpa [extendDecisionTreeAt_zero] using hj
    have heval := jointProb_zero_support_univ μ T base target hjAt
    unfold DecisionTree.evalR
    rw [heval, sub_self, zero_pow (by norm_num), zero_mul]

theorem causalPairEnergy_card_eq_two_var
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) :
    causalPairEnergy μ T (Fintype.card E) = 2 * Lindeberg.var μ T.evalR := by
  unfold causalPairEnergy
  simp_rw [jointProb_extendDecisionTreeAt_card_eq_mul_mass μ hpos hμ1 T]
  have hreorder :
      (∑ base, ∑ target, (T.evalR base - T.evalR target) ^ 2 *
          (μ base * μ target)) =
        ∑ base, ∑ target, μ base * μ target *
          (T.evalR base - T.evalR target) ^ 2 := by
    apply Finset.sum_congr rfl
    intro base _
    apply Finset.sum_congr rfl
    intro target _
    ring
  rw [hreorder]
  rw [Lindeberg.var_eq_double_sum μ hμ1 T.evalR]
  ring


theorem causalPairEnergy_succ_sub (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (T : DecisionTree E) (t : ℕ) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t =
      ∑ base, ∑ left, ∑ right,
        ((T.evalR base - T.evalR right) ^ 2 -
          (T.evalR base - T.evalR left) ^ 2) *
        tripleJointProb μ ∅ base left right
          (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
  have hleft :
      (∑ base, ∑ left, ∑ right,
          (T.evalR base - T.evalR left) ^ 2 *
            tripleJointProb μ ∅ base left right
              (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E))) =
        causalPairEnergy μ T t := by
    unfold causalPairEnergy
    apply Finset.sum_congr rfl
    intro base _
    apply Finset.sum_congr rfl
    intro left _
    rw [← Finset.mul_sum]
    rw [sum_tripleJointProb_right_eq_jointProb μ hpos base left base]
    rw [extendDecisionTreeTriple_leftOrder]
  have hright :
      (∑ base, ∑ left, ∑ right,
          (T.evalR base - T.evalR right) ^ 2 *
            tripleJointProb μ ∅ base left right
              (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E))) =
        causalPairEnergy μ T (t + 1) := by
    unfold causalPairEnergy
    apply Finset.sum_congr rfl
    intro base _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro right _
    rw [← Finset.mul_sum]
    rw [sum_tripleJointProb_left_eq_jointProb μ hpos base right base]
    rw [extendDecisionTreeTriple_rightOrder]
  rw [← hright, ← hleft]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro base _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro right _
  ring

lemma evalR_sqdiff_sub_sqdiff_le_abs (T : DecisionTree E)
    (base left right : ConfigSpace E) :
    (T.evalR base - T.evalR right) ^ 2 -
        (T.evalR base - T.evalR left) ^ 2 ≤
      |T.evalR right - T.evalR left| := by
  unfold DecisionTree.evalR
  cases hb : T.eval base <;> cases hl : T.eval left <;> cases hr : T.eval right <;>
    norm_num

lemma tripleJointProb_nonneg (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    0 ≤ tripleJointProb μ ∅ base left right S := by
  rw [← pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb
    μ hpos S base left right]
  exact ENNReal.toReal_nonneg

theorem causalPairEnergy_succ_sub_le_abs
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
      ∑ base, ∑ left, ∑ right, |T.evalR right - T.evalR left| *
        tripleJointProb μ ∅ base left right
          (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
  rw [causalPairEnergy_succ_sub μ hpos T t]
  apply Finset.sum_le_sum
  intro base _
  apply Finset.sum_le_sum
  intro left _
  apply Finset.sum_le_sum
  intro right _
  exact mul_le_mul_of_nonneg_right
    (evalR_sqdiff_sub_sqdiff_le_abs T base left right)
    (tripleJointProb_nonneg μ hpos _ base left right)

end AdaptiveCausalKernel
end OSSS
end StatMech
