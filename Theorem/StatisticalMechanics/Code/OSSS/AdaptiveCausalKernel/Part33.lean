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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part33
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


lemma evalR_pair_energy_diff_le_abs (T : DecisionTree E)
    (base left right : ConfigSpace E) :
    (T.evalR base - T.evalR right) ^ 2 -
        (T.evalR base - T.evalR left) ^ 2 ≤
      |T.evalR right - T.evalR left| := by
  unfold DecisionTree.evalR
  cases hb : T.eval base <;> cases hl : T.eval left <;>
    cases hr : T.eval right <;> simp [hb, hl, hr] <;> norm_num


lemma abs_evalR_sub_eq_disagreement (T : DecisionTree E)
    (left right : ConfigSpace E) :
    |T.evalR right - T.evalR left| =
      T.evalR right + T.evalR left - 2 * T.evalR right * T.evalR left := by
  unfold DecisionTree.evalR
  cases hl : T.eval left <;> cases hr : T.eval right <;>
    simp [hl, hr] <;> norm_num


theorem causalTripleJump_eq_disagreement
    (μ : ConfigSpace E → ℝ) (T : DecisionTree E) (t : ℕ)
    (seed : ConfigSpace E) :
    causalTripleJump μ T t seed =
      let S := extendDecisionTreeTriple (some t) T seed
        (Finset.univ : Finset E)
      ∑ base, ∑ left, ∑ right,
        (T.evalR right + T.evalR left -
          2 * T.evalR right * T.evalR left) *
            tripleJointProb μ ∅ base left right S := by
  unfold causalTripleJump
  simp_rw [abs_evalR_sub_eq_disagreement]


theorem causalPairEnergy_sub_le_causalTripleJump
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (T : DecisionTree E) (t : ℕ) (seed : ConfigSpace E) :
    causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤
      causalTripleJump μ T t seed := by
  rw [← tripleJoint_right_energy_eq_causalPairEnergy μ hpos T t seed]
  rw [← tripleJoint_left_energy_eq_causalPairEnergy μ hpos T t seed]
  unfold causalTripleJump
  simp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro base _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro left _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro right _
  rw [← sub_mul]
  exact mul_le_mul_of_nonneg_right
    (evalR_pair_energy_diff_le_abs T base left right)
    (tripleJointProb_nonneg μ hpos _ base left right)


theorem two_var_le_sum_causalTripleJump
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (seed : ConfigSpace E) :
    2 * Lindeberg.var μ T.evalR ≤
      ∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed := by
  have hsum :
      (∑ t ∈ Finset.range (Fintype.card E),
        (causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t)) ≤
      ∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed :=
    Finset.sum_le_sum fun t _ =>
      causalPairEnergy_sub_le_causalTripleJump μ hpos T t seed
  rw [Finset.sum_range_sub (fun t => causalPairEnergy μ T t) (Fintype.card E)] at hsum
  rw [causalPairEnergy_zero, causalPairEnergy_card_eq_two_var μ hpos hμ1] at hsum
  simpa using hsum


theorem adaptive_tree_osss_of_causalTripleJump_le
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (seed : ConfigSpace E)
    (hjump : ∀ t < Fintype.card E,
      causalTripleJump μ T t seed ≤
        2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
          Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
    Lindeberg.var μ T.evalR ≤
      ∑ e, LindebergTree.revealmentMu μ T e *
        Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
  have htel := two_var_le_sum_causalTripleJump μ hpos hμ1 T seed
  have hsteps :
      (∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed) ≤
        ∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) :=
    Finset.sum_le_sum fun t ht => hjump t (Finset.mem_range.mp ht)
  have hmain := htel.trans hsteps
  have hreorder :
      (∑ t ∈ Finset.range (Fintype.card E),
          2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) *
            Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) =
        2 * ∑ e, LindebergTree.revealmentMu μ T e *
          Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    apply congrArg (fun z : ℝ => 2 * z)
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    rw [sum_mean_sharedStepIndicator_eq_revealmentMu]
    ring
  rw [hreorder] at hmain
  linarith


theorem targetProb_eq_condMass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (base target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    targetProb μ F base target S = condMass μ F target target := by
  induction S generalizing F base with
  | done =>
      have hFu : F = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro e
        by_contra he
        have : e ∈ (∅ : Finset E) := by
          rw [hR]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he⟩
        simp at this
      subst F
      unfold targetProb condMass
      rw [if_pos (agree_self Finset.univ target), condNorm_univ]
      field_simp [(hpos target).ne']
  | @node R e he active closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext z
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      rw [targetProb]
      rw [ihc (insert e F) (Function.update base e false) hchild]
      rw [iho (insert e F) (Function.update base e true) hchild]
      rw [← add_mul, splitWeight_sum_base]
      unfold bitWeight
      rw [← condProbBit_eq_closed_or_one_sub μ hpos F target e]
      exact (condMass_chain_step μ hpos F target e heF).symm


theorem targetProb_empty_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    targetProb μ ∅ base target S = μ target := by
  rw [targetProb_eq_condMass μ hpos ∅ base target S (by simp)]
  unfold condMass
  rw [if_pos]
  · rw [condNorm_empty, hμ1]
    ring
  · exact agree_self ∅ target

theorem sum_tripleProb_right_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, tripleProb μ ∅ base left right S = μ left := by
  have h := baseSum_tripleProb_right_eq_targetProb μ hpos ∅ base left seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base left S.leftOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_tripleProb_left_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, tripleProb μ ∅ base left right S = μ right := by
  have h := baseSum_tripleProb_left_eq_targetProb μ hpos ∅ base right seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base right S.rightOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_crossTripleProb_right_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base left seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ right, crossTripleProb μ ∅ base left right S = μ left := by
  have h := baseSum_crossTripleProb_right_eq_targetProb μ hpos ∅ base left seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base left S.leftOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_crossTripleProb_left_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base right seed : ConfigSpace E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    ∑ left, crossTripleProb μ ∅ base left right S = μ right := by
  have h := baseSum_crossTripleProb_left_eq_targetProb μ hpos ∅ base right seed S (by simp)
  rw [targetProb_empty_eq_mass μ hpos hμ1 base right S.rightOrder] at h
  simpa [baseSum, Agree] using h

theorem sum_jointProb_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base, jointProb μ ∅ base target S = μ target := by
  rw [sum_jointProb_empty_eq_targetProb μ seed target S]
  exact targetProb_empty_eq_mass μ hpos hμ1 seed target S

theorem sum_frozenCodeAtom_mass_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base,
      (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = μ target := by
  simp_rw [pairedCube_frozenCodeAtom_toReal_eq_jointProb μ hpos]
  exact sum_jointProb_empty_eq_mass μ hpos hμ1 seed target S

theorem sum_frozenCodeAtom_observable_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (seed : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ℝ) :
    ∑ base, ∑ target, g target *
      (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
        Lindeberg.mean μ g := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro target _
  rw [← Finset.mul_sum]
  rw [sum_frozenCodeAtom_mass_eq_mass μ hpos hμ1 seed target S]


theorem sum_targetProb_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetProb μ ∅ base target S =
      Lindeberg.mean μ g := by
  simp_rw [targetProb_empty_eq_mass μ hpos hμ1 base]
  rfl


theorem targetIntegral_empty_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base target : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E)) :
    targetIntegral μ ∅ base target S = μ target := by
  rw [targetIntegral_eq_targetProb μ hpos]
  exact targetProb_empty_eq_mass μ hpos hμ1 base target S


theorem sum_diag_targetIntegral_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (base : ConfigSpace E) (S : CausalOrder (Finset.univ : Finset E))
    (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target S =
      Lindeberg.mean μ g := by
  simp_rw [targetIntegral_empty_eq_mass μ hpos hμ1 base]
  rfl


theorem decisionTree_mixed_targetIntegral_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (base target : ConfigSpace E) :
    targetIntegral μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = μ target :=
  targetIntegral_empty_eq_mass μ hpos hμ1 base target _


theorem decisionTree_mixed_diag_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (base : ConfigSpace E) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target
      (extendDecisionTree T base (Finset.univ : Finset E)) = Lindeberg.mean μ g :=
  sum_diag_targetIntegral_eq_mean μ hpos hμ1 base _ g


theorem decisionTreeAt_mixed_targetIntegral_eq_mass (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (t : ℕ) (T : DecisionTree E) (base target : ConfigSpace E) :
    targetIntegral μ ∅ base target
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = μ target :=
  targetIntegral_empty_eq_mass μ hpos hμ1 base target _


theorem decisionTreeAt_mixed_diag_eq_mean (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (t : ℕ) (T : DecisionTree E) (base : ConfigSpace E) (g : ConfigSpace E → ℝ) :
    ∑ target, g target * targetIntegral μ ∅ base target
      (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = Lindeberg.mean μ g :=
  sum_diag_targetIntegral_eq_mean μ hpos hμ1 base _ g


end AdaptiveCausalKernel
end OSSS
end StatMech
