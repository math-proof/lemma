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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part30
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


theorem targetIntegral_eq_targetProb (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (base target : ConfigSpace E)
    {R : Finset E} (S : CausalOrder R) :
    targetIntegral μ F base target S = targetProb μ F base target S := by
  induction S generalizing F base with
  | done => rfl
  | @node R e he active closed opened ihc iho =>
      rw [targetIntegral, targetProb]
      have ha : 0 ≤ condProbClosed μ F base e ∧ condProbClosed μ F base e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F base e false
          (condNorm_pos hpos F base),
          condProbBit_le_one (fun ω => (hpos ω).le) F base e false
          (condNorm_pos hpos F base)⟩
      have hq : 0 ≤ condProbClosed μ F target e ∧ condProbClosed μ F target e ≤ 1 := by
        unfold condProbClosed
        exact ⟨condProbBit_nonneg (fun ω => (hpos ω).le) F target e false
          (condNorm_pos hpos F target),
          condProbBit_le_one (fun ω => (hpos ω).le) F target e false
          (condNorm_pos hpos F target)⟩
      by_cases hactive : active
      · simp only [hactive, if_true, splitWeight, independentWeight]
        rw [volume_thresholdInterval _ ha.1 ha.2 false]
        rw [volume_thresholdInterval _ ha.1 ha.2 true]
        rw [volume_thresholdInterval _ hq.1 hq.2 (target e)]
        rw [ihc, iho]
      · simp only [hactive, Bool.false_eq_true, if_false, splitWeight]
        rw [volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 false (target e)]
        rw [volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 true (target e)]
        rw [ihc, iho]


theorem sum_pairedCube_frozenCodeAtom_eq_targetIntegral
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (seed target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    ∑ base : ConfigSpace E,
        (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal =
      targetIntegral μ ∅ seed target S := by
  simp_rw [pairedCube_frozenCodeAtom_toReal_eq_jointProb μ hpos]
  rw [targetIntegral_eq_targetProb μ hpos]
  rw [← baseSum_jointProb_eq_targetProb μ ∅ seed target S (by simp)]
  unfold baseSum
  simp [Agree]


lemma condMass_chain_step (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (target : ConfigSpace E) (e : E) (he : e ∉ F) :
    condMass μ F target target =
      condProbBit μ F target e (target e) *
        condMass μ (insert e F) target target := by
  unfold condMass
  rw [if_pos (agree_self F target), if_pos (agree_self (insert e F) target)]
  rw [condProbBit_eq_ratio]
  have hF := (condNorm_pos hpos F target).ne'
  have hI := (condNorm_pos hpos (insert e F) target).ne'
  field_simp

lemma condProbBit_eq_closed_or_one_sub (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (target : ConfigSpace E) (e : E) :
    condProbBit μ F target e (target e) =
      if target e then 1 - condProbClosed μ F target e
      else condProbClosed μ F target e := by
  by_cases hb : target e
  · simp only [hb, if_true]
    have hsum := condProbBit_true_add_false μ F target e
      (condNorm_pos hpos F target).ne'
    unfold condProbClosed
    linarith
  · simp only [hb, Bool.false_eq_true, if_false]
    rfl

theorem condObservable_split (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (F : Finset E) (seed : ConfigSpace E)
    (g : ConfigSpace E → ℝ) (e : E) (he : e ∉ F) :
    condObservable μ F seed g =
      bitWeight (condProbClosed μ F seed e) false *
          condObservable μ (insert e F) (Function.update seed e false) g +
        bitWeight (condProbClosed μ F seed e) true *
          condObservable μ (insert e F) (Function.update seed e true) g := by
  unfold condObservable
  rw [baseSum_split F seed
    (fun target => g target * condMass μ F target target) e he]
  have hbranch (b : Bool) :
      baseSum (insert e F) (Function.update seed e b)
          (fun target => g target * condMass μ F target target) =
        bitWeight (condProbClosed μ F seed e) b *
          baseSum (insert e F) (Function.update seed e b)
            (fun target => g target *
              condMass μ (insert e F) target target) := by
    unfold baseSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    by_cases hA : Agree (insert e F) (Function.update seed e b) target
    · have hbit : target e = b := by
        have h := hA e (Finset.mem_insert_self e F)
        simpa using h
      have hag : Agree F seed target := by
        intro x hx
        have hxe : x ≠ e := fun hxe => he (hxe ▸ hx)
        have h := hA x (Finset.mem_insert_of_mem hx)
        rw [Function.update_of_ne hxe] at h
        exact h
      have hq : condProbClosed μ F target e = condProbClosed μ F seed e :=
        condProbClosed_congr μ F target seed e (fun x hx => hag x hx)
      simp only [hA, if_true]
      rw [condMass_chain_step μ hpos F target e he]
      rw [condProbBit_eq_closed_or_one_sub μ hpos F target e, hbit, hq]
      cases b <;> simp [bitWeight] <;> ring
    · simp [hA]
  rw [hbranch false, hbranch true]

theorem condObservable_empty_eq_mean (μ : ConfigSpace E → ℝ)
    (hμ1 : ∑ ω, μ ω = 1) (g : ConfigSpace E → ℝ)
    (seed : ConfigSpace E) :
    condObservable μ ∅ seed g = Lindeberg.mean μ g := by
  unfold condObservable baseSum Lindeberg.mean condMass
  apply Finset.sum_congr rfl
  intro target _
  simp [Agree, condNorm_empty, hμ1]

theorem baseSum_flip_condMass_eq_flipBaseProb
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (seed : ConfigSpace E) (z : E) {R : Finset E}
    (S : TripleOrder R) (hR : R = Finset.univ \ F) :
    baseSum F seed (fun base =>
      (if tripleModeAt S base z = .flip then 1 else 0) *
        condMass μ F base base) = flipBaseProb μ F seed z S := by
  induction S generalizing F seed with
  | done => simp [baseSum, tripleModeAt, flipBaseProb]
  | @node R e he mode closed opened ihc iho =>
      have heF : e ∉ F := by
        intro heMem
        have : e ∈ Finset.univ \ F := by rw [← hR]; exact he
        exact (Finset.mem_sdiff.mp this).2 heMem
      have hchild : R.erase e = Finset.univ \ insert e F := by
        rw [hR]
        ext x
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_insert]
        tauto
      by_cases hze : z = e
      · subst z
        by_cases hm : mode = .flip
        · subst mode
          simp only [tripleModeAt, if_pos rfl, if_true, one_mul]
          rw [baseSum_condMass_self_eq_one μ hpos F seed]
          simp [flipBaseProb]
        · have hm' : mode ≠ TripleMode.flip := hm
          simp only [tripleModeAt, if_pos rfl, hm', if_false, zero_mul]
          simp [baseSum, flipBaseProb, hm']
      · rw [baseSum_split F seed (fun base =>
          (if tripleModeAt (.node e he mode closed opened) base z = .flip
            then 1 else 0) * condMass μ F base base) e heF]
        have hbranch (b : Bool) :
            baseSum (insert e F) (Function.update seed e b)
                (fun base =>
                  (if tripleModeAt (.node e he mode closed opened) base z = .flip
                    then 1 else 0) * condMass μ F base base) =
              bitWeight (condProbClosed μ F seed e) b *
                baseSum (insert e F) (Function.update seed e b)
                  (fun base =>
                    (if tripleModeAt (if b then opened else closed) base z = .flip
                      then 1 else 0) *
                      condMass μ (insert e F) base base) := by
          unfold baseSum
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro base _
          by_cases hA : Agree (insert e F) (Function.update seed e b) base
          · have hbit : base e = b := by
              have h := hA e (Finset.mem_insert_self e F)
              simpa using h
            have hag : Agree F seed base := by
              intro x hx
              have hxe : x ≠ e := fun hxe => heF (hxe ▸ hx)
              have h := hA x (Finset.mem_insert_of_mem hx)
              rw [Function.update_of_ne hxe] at h
              exact h
            have hq : condProbClosed μ F base e = condProbClosed μ F seed e :=
              condProbClosed_congr μ F base seed e (fun x hx => hag x hx)
            simp only [hA, if_true]
            rw [condMass_chain_step μ hpos F base e heF]
            rw [condProbBit_eq_closed_or_one_sub μ hpos F base e, hbit, hq]
            cases b
            · by_cases hm : tripleModeAt closed base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, bitWeight, mul_assoc]
            · by_cases hm : tripleModeAt opened base z = .flip <;>
                simp [tripleModeAt, hze, hbit, hm, bitWeight, mul_assoc]
          · simp [hA]
        rw [hbranch false, hbranch true]
        simp only [Bool.false_eq_true, if_false, if_true]
        rw [ihc (insert e F) (Function.update seed e false) hchild]
        rw [iho (insert e F) (Function.update seed e true) hchild]
        simp [flipBaseProb, hze]

theorem flipBaseProb_empty_eq_mean_flip
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (seed : ConfigSpace E) (z : E)
    (S : TripleOrder (Finset.univ : Finset E)) :
    flipBaseProb μ ∅ seed z S =
      Lindeberg.mean μ (fun base =>
        if tripleModeAt S base z = .flip then 1 else 0) := by
  rw [← baseSum_flip_condMass_eq_flipBaseProb μ hpos ∅ seed z S (by simp)]
  unfold baseSum Lindeberg.mean condMass
  apply Finset.sum_congr rfl
  intro base _
  simp [Agree, condNorm_empty, hμ1]

theorem flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (seed : ConfigSpace E) (t : ℕ) (z : E) :
    flipBaseProb μ ∅ seed z
        (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) =
      Lindeberg.mean μ (fun base => sharedStepIndicator T base t z) := by
  rw [flipBaseProb_empty_eq_mean_flip μ hpos hμ1 seed z]
  unfold Lindeberg.mean
  apply Finset.sum_congr rfl
  intro base _
  change (if tripleModeAt
      (extendDecisionTreeTriple (some t) T seed Finset.univ) base z = .flip
      then 1 else 0) * μ base = sharedStepIndicator T base t z * μ base
  rw [sharedStepIndicator_eq_tripleFlipIndicator]
  unfold tripleFlipIndicator
  rw [extendDecisionTreeTriple_univ_seed_congr (some t) T base seed]

theorem targetProb_eq_condMass_core (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
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


theorem flipTripleProb_right_marginal_extendDecisionTreeTriple
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (driver left rightSeed : ConfigSpace E) (z : E)
    (t : ℕ) (T : DecisionTree E) (known : ConfigSpace E) (R : Finset E)
    (hR : R = Finset.univ \ F) :
    baseSum F rightSeed (fun right =>
      flipTripleProb μ F driver left right z
        (extendDecisionTreeTriple (some t) T known R)) =
      condMass μ F left left *
        flipBaseProb μ F driver z
          (extendDecisionTreeTriple (some t) T known R) := by
  induction T generalizing t F driver rightSeed known R with
  | leaf b => simp [extendDecisionTreeTriple, baseSum]
  | node q opened closed iho ihc =>
      rw [extendDecisionTreeTriple]
      by_cases hqR : q ∈ R
      · rw [dif_pos hqR]
        have hqF : q ∉ F := by
          intro hqF
          have : q ∈ Finset.univ \ F := by rw [← hR]; exact hqR
          exact (Finset.mem_sdiff.mp this).2 hqF
        have hchild : R.erase q = Finset.univ \ insert q F := by
          rw [hR]
          ext x
          simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ,
            true_and, Finset.mem_insert]
          tauto
        cases t with
        | zero =>
            by_cases hzq : z = q
            · subst z
              simp only [flipTripleProb, if_pos rfl, if_true, flipBaseProb, one_mul]
              rw [baseSum_tripleProb_right_eq_targetProb μ hpos F driver left rightSeed
                (.node q hqR .flip
                  (extendDecisionTreeTriple none closed
                    (Function.update known q false) (R.erase q))
                  (extendDecisionTreeTriple none opened
                    (Function.update known q true) (R.erase q))) hR]
              rw [targetProb_eq_condMass_core μ hpos F driver left]
              · ring
              · exact hR
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
        | succ t =>
            by_cases hzq : z = q
            · simp [flipTripleProb, flipBaseProb, hzq, baseSum]
            · rw [baseSum_split F rightSeed (fun right =>
                flipTripleProb μ F driver left right z
                  (.node q hqR .before
                    (extendDecisionTreeTriple (some t) closed
                      (Function.update known q false) (R.erase q))
                    (extendDecisionTreeTriple (some t) opened
                      (Function.update known q true) (R.erase q)))) q hqF]
              have hbranch (b : Bool) :
                  baseSum (insert q F) (Function.update rightSeed q b)
                    (fun right => flipTripleProb μ F driver left right z
                      (.node q hqR .before
                        (extendDecisionTreeTriple (some t) closed
                          (Function.update known q false) (R.erase q))
                        (extendDecisionTreeTriple (some t) opened
                          (Function.update known q true) (R.erase q)))) =
                    overlapWeight (condProbClosed μ F left q)
                        (condProbClosed μ F rightSeed q) (left q) b *
                      (bitWeight (condProbClosed μ F driver q) false *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipTripleProb μ (insert q F)
                            (Function.update driver q false) left right z
                            (extendDecisionTreeTriple (some t) closed
                              (Function.update known q false) (R.erase q))) +
                       bitWeight (condProbClosed μ F driver q) true *
                        baseSum (insert q F) (Function.update rightSeed q b)
                          (fun right => flipTripleProb μ (insert q F)
                            (Function.update driver q true) left right z
                            (extendDecisionTreeTriple (some t) opened
                              (Function.update known q true) (R.erase q)))) := by
                unfold baseSum
                rw [mul_add]
                simp_rw [Finset.mul_sum]
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro right _
                by_cases hA : Agree (insert q F) (Function.update rightSeed q b) right
                · have hbit : right q = b := by
                    have h := hA q (Finset.mem_insert_self q F)
                    simpa using h
                  have hag : Agree F rightSeed right := by
                    intro x hx
                    have hxq : x ≠ q := fun hxq => hqF (hxq ▸ hx)
                    have h := hA x (Finset.mem_insert_of_mem hx)
                    rw [Function.update_of_ne hxq] at h
                    exact h
                  have hr : condProbClosed μ F right q =
                      condProbClosed μ F rightSeed q :=
                    condProbClosed_congr μ F right rightSeed q (fun x hx => hag x hx)
                  simp only [hA, if_true]
                  rw [flipTripleProb, hr, hbit]
                  simp [tripleWeight, hzq, mul_add, mul_assoc]
                  ring
                · simp [hA]
              rw [hbranch false, hbranch true]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q false) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q false) t (Function.update known q true)
                (R.erase q) hchild]
              rw [ihc (insert q F) (Function.update driver q false)
                (Function.update rightSeed q true) t (Function.update known q false)
                (R.erase q) hchild]
              rw [iho (insert q F) (Function.update driver q true)
                (Function.update rightSeed q true) t (Function.update known q true)
                (R.erase q) hchild]
              have hchain := condMass_chain_step μ hpos F left q hqF
              rw [condProbBit_eq_closed_or_one_sub μ hpos F left q] at hchain
              simp only [flipBaseProb, hzq, if_false, bitWeight]
              rw [← add_mul]
              rw [overlapWeight_sum_target]
              by_cases hlq : left q <;> simp [hlq, bitWeight] at hchain ⊢ <;>
                rw [hchain] <;> ring
      · rw [dif_neg hqR]
        by_cases hkq : known q
        · simp only [hkq, if_true]
          exact iho F driver rightSeed t known R hR
        · simp only [hkq, Bool.false_eq_true, if_false]
          exact ihc F driver rightSeed t known R hR


theorem pathProb_eq_condMass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (F : Finset E) (driver target : ConfigSpace E) {R : Finset E}
    (S : CausalOrder R) (hR : R = Finset.univ \ F) :
    pathProb μ F driver target S = condMass μ F target target := by
  induction S generalizing F with
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
      unfold pathProb condMass
      rw [if_pos (agree_self Finset.univ target), condNorm_univ]
      field_simp [(hpos target).ne']
  | @node R e he independent closed opened ihc iho =>
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
      have hrec :
          (if driver e then
              pathProb μ (insert e F) driver target opened
            else pathProb μ (insert e F) driver target closed) =
            condMass μ (insert e F) target target := by
        by_cases hb : driver e
        · simp only [hb, if_true]
          exact iho (insert e F) hchild
        · simp only [hb, Bool.false_eq_true, if_false]
          exact ihc (insert e F) hchild
      rw [pathProb, hrec]
      have hw : bitWeight (condProbClosed μ F target e) (target e) =
          condProbBit μ F target e (target e) := by
        rw [condProbBit_eq_closed_or_one_sub μ hpos F target e]
        rfl
      rw [hw]
      exact (condMass_chain_step μ hpos F target e heF).symm

theorem pathProb_empty_eq_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (driver target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    pathProb μ ∅ driver target S = μ target := by
  rw [pathProb_eq_condMass μ hpos ∅ driver target S (by simp)]
  unfold condMass
  rw [if_pos (agree_self ∅ target), condNorm_empty, hμ1]
  ring


theorem jointProb_allIndependent_empty_eq_mul_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (base target : ConfigSpace E)
    (S : CausalOrder (Finset.univ : Finset E)) :
    jointProb μ ∅ base target (allIndependent S) = μ base * μ target := by
  rw [jointProb_allIndependent_eq_mul_pathProb]
  rw [pathProb_empty_eq_mass μ hpos hμ1, pathProb_empty_eq_mass μ hpos hμ1]

theorem jointProb_extendDecisionTreeAt_card_eq_mul_mass
    (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E)
    (base target : ConfigSpace E) :
    jointProb μ ∅ base target
        (extendDecisionTreeAt (Fintype.card E) T base (Finset.univ : Finset E)) =
      μ base * μ target := by
  rw [extendDecisionTreeAt_card_univ_eq_allIndependent]
  exact jointProb_allIndependent_empty_eq_mul_mass μ hpos hμ1 base target _


end AdaptiveCausalKernel
end OSSS
end StatMech
