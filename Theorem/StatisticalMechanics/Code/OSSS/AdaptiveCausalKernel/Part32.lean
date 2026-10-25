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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part32
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


theorem tree_osss_of_causal_step_bound
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (hStep : ∀ t < Fintype.card E,
      causalAbsJump μ T t ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
    Lindeberg.var μ T.evalR ≤
      ∑ e, LindebergTree.revealmentMu μ T e *
        Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
  have hinc : ∀ t < Fintype.card E,
      causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) := by
    intro t ht
    exact (causalPairEnergy_succ_sub_le_abs μ hpos T t).trans (hStep t ht)
  have hsum := Finset.sum_le_sum (fun t ht => hinc t (Finset.mem_range.mp ht))
  have hleft :
      ∑ t ∈ Finset.range (Fintype.card E),
          (causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t) =
        2 * Lindeberg.var μ T.evalR := by
    rw [Finset.sum_range_sub]
    rw [causalPairEnergy_zero, causalPairEnergy_card_eq_two_var μ hpos hμ1]
    ring
  have hright :
      ∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) =
        2 * ∑ e, LindebergTree.revealmentMu μ T e *
          Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
    apply congrArg (fun x : ℝ => 2 * x)
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    rw [sum_mean_sharedStepIndicator_eq_revealmentMu]
    ring
  rw [hleft, hright] at hsum
  linarith


theorem tripleJoint_left_energy_eq_causalPairEnergy
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    ∑ base, ∑ left, ∑ right,
        (T.evalR base - T.evalR left) ^ 2 *
          tripleJointProb μ ∅ base left right S =
      causalPairEnergy μ T t := by
  dsimp only
  unfold causalPairEnergy
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.sum_congr rfl
  intro left _
  rw [← Finset.mul_sum]
  have hm := baseSum_tripleJointProb_right_eq_jointProb
    μ hpos ∅ base left seed
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) (by simp)
  have hm' : ∑ right, tripleJointProb μ ∅ base left right
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
        jointProb μ ∅ base left
          (extendDecisionTreeTriple (some t) T seed
            (Finset.univ : Finset E)).leftOrder := by
    simpa [baseSum, Agree] using hm
  rw [hm']
  rw [extendDecisionTreeTriple_leftOrder]
  rw [extendDecisionTreeAt_univ_seed_congr t T seed base]


theorem tripleJoint_right_energy_eq_causalPairEnergy
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    let S := extendDecisionTreeTriple (some t) T seed
      (Finset.univ : Finset E)
    ∑ base, ∑ left, ∑ right,
        (T.evalR base - T.evalR right) ^ 2 *
          tripleJointProb μ ∅ base left right S =
      causalPairEnergy μ T (t + 1) := by
  dsimp only
  unfold causalPairEnergy
  apply Finset.sum_congr rfl
  intro base _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  rw [← Finset.mul_sum]
  have hm := baseSum_tripleJointProb_left_eq_jointProb
    μ hpos ∅ base right seed
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) (by simp)
  have hm' : ∑ left, tripleJointProb μ ∅ base left right
      (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
        jointProb μ ∅ base right
          (extendDecisionTreeTriple (some t) T seed
            (Finset.univ : Finset E)).rightOrder := by
    simpa [baseSum, Agree] using hm
  rw [hm']
  rw [extendDecisionTreeTriple_rightOrder]
  rw [extendDecisionTreeAt_univ_seed_congr (t + 1) T seed base]

end AdaptiveCausalKernel
end OSSS
end StatMech
