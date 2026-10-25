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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part17
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


lemma frozenTripleRawPair_toReal_eq_tripleWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) (i : Fin (Fintype.card E)) :
    (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (frozenTripleRawPair mu S base left right i)).toReal =
      tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
        (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
        (base (realizedEquiv S.leftOrder base i))
        (left (realizedEquiv S.leftOrder base i))
        (right (realizedEquiv S.leftOrder base i)) := by
  let sigma := realizedEquiv S.leftOrder base
  have hsigma : realizedEquiv S.leftOrder base = sigma := rfl
  unfold frozenTripleRawPair frozenRawPair
  rw [← realizedEquiv_leftOrder_eq_rightOrder S base]
  simp only [hsigma, independentAt_leftOrder, independentAt_rightOrder]
  cases hm : tripleModeAt S base (sigma i) with
  | before =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        if_true, Set.prod_inter_prod, Set.inter_self, tripleWeight]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_toReal_eq_bitWeight mu hpos,
        rawInterval_inter_toReal_eq_overlapWeight mu hpos]
  | flip =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        Bool.false_eq_true, if_false, if_true, Set.prod_inter_prod,
        Set.inter_univ, Set.inter_assoc, tripleWeight]
      have hset : GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
          (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i) =
          GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i := by
        ext x
        simp only [Set.mem_inter_iff]
        tauto
      rw [hset, Set.univ_inter]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_inter_toReal_eq_overlapWeight mu hpos,
        rawInterval_toReal_eq_bitWeight mu hpos]
  | after =>
      simp only [hm, TripleMode.leftIndependent, TripleMode.rightIndependent,
        Bool.false_eq_true, if_false, Set.prod_inter_prod, Set.inter_univ,
        tripleWeight, tripleOverlapWeight]
      have hset :
          (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
              GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i) ∩
            (GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
              GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) right i) =
          GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) base i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) left i ∩
            GrandCoupling.rawInterval mu (sigma : Fin (Fintype.card E) → E) right i := by
        ext x
        simp only [Set.mem_inter_iff]
        tauto
      rw [hset]
      rw [Measure.prod_prod, ENNReal.toReal_mul,
        rawInterval_tripleInter_toReal_eq_tripleOverlapWeight mu hpos]
      simp

theorem pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : TripleOrder (Finset.univ : Finset E))
    (base left right : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right)).toReal =
      ∏ i : Fin (Fintype.card E),
        tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i))
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i)
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i)
          (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i)
          (base (realizedEquiv S.leftOrder base i))
          (left (realizedEquiv S.leftOrder base i))
          (right (realizedEquiv S.leftOrder base i)) := by
  rw [pairedCube_frozenTripleCodeAtom, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact frozenTripleRawPair_toReal_eq_tripleWeight mu hpos S base left right i

lemma thresholdInterval_subset_Ico (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    thresholdInterval q b ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  cases b
  · simp only [thresholdInterval, Bool.false_eq_true, if_false, Set.mem_Ico] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hq1⟩
  · simp only [thresholdInterval, if_true, Set.mem_Ico] at hx ⊢
    exact ⟨le_trans hq0 hx.1, hx.2⟩

lemma tripleOverlapWeight_sum_third (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    tripleOverlapWeight a q r b y false + tripleOverlapWeight a q r b y true =
      overlapWeight a q b y := by
  unfold tripleOverlapWeight
  have hA : MeasurableSet (thresholdInterval a b ∩ thresholdInterval q y) := by
    cases b <;> cases y <;> simp [thresholdInterval]
  have hsub : thresholdInterval a b ∩ thresholdInterval q y ⊆ Set.Ico (0 : ℝ) 1 :=
    fun _ hx => thresholdInterval_subset_Ico a ha0 ha1 b hx.1
  rw [volume_inter_threshold_false_add_true _ hA hsub r hr0 hr1]
  exact volume_thresholdInterval_inter a q ha0 ha1 hq0 hq1 b y

lemma tripleOverlapWeight_sum_second (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    tripleOverlapWeight a q r b false z + tripleOverlapWeight a q r b true z =
      overlapWeight a r b z := by
  unfold tripleOverlapWeight
  have hcomm : ∀ y : Bool,
      thresholdInterval a b ∩ thresholdInterval q y ∩ thresholdInterval r z =
        (thresholdInterval a b ∩ thresholdInterval r z) ∩ thresholdInterval q y := by
    intro y
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  rw [hcomm false, hcomm true]
  have hA : MeasurableSet (thresholdInterval a b ∩ thresholdInterval r z) := by
    cases b <;> cases z <;> simp [thresholdInterval]
  have hsub : thresholdInterval a b ∩ thresholdInterval r z ⊆ Set.Ico (0 : ℝ) 1 :=
    fun _ hx => thresholdInterval_subset_Ico a ha0 ha1 b hx.1
  rw [volume_inter_threshold_false_add_true _ hA hsub q hq0 hq1]
  exact volume_thresholdInterval_inter a r ha0 ha1 hr0 hr1 b z

lemma tripleWeight_sum_third (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b y : Bool) :
    tripleWeight mode a q r b y false + tripleWeight mode a q r b y true =
      splitWeight mode.leftIndependent a q b y := by
  cases mode with
  | before =>
      simp only [tripleWeight, TripleMode.leftIndependent, splitWeight, if_true]
      rw [← mul_add, overlapWeight_comm q r y false, overlapWeight_comm q r y true,
        overlapWeight_sum_base, bitWeight]
      rfl
  | flip =>
      simp only [tripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      rw [← mul_add, bitWeight_false_add_true, mul_one]
  | after =>
      simp only [tripleWeight, TripleMode.leftIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_third a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

lemma tripleWeight_sum_second (mode : TripleMode) (a q r : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (b z : Bool) :
    tripleWeight mode a q r b false z + tripleWeight mode a q r b true z =
      splitWeight mode.rightIndependent a r b z := by
  cases mode with
  | before =>
      simp only [tripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← mul_add, overlapWeight_sum_base]
      unfold independentWeight
      rfl
  | flip =>
      simp only [tripleWeight, TripleMode.rightIndependent, splitWeight, if_true]
      rw [← add_mul, overlapWeight_comm a q b false, overlapWeight_comm a q b true,
        overlapWeight_sum_base]
      rfl
  | after =>
      simp only [tripleWeight, TripleMode.rightIndependent, Bool.false_eq_true,
        splitWeight, if_false]
      exact tripleOverlapWeight_sum_second a q r ha0 ha1 hq0 hq1 hr0 hr1 b z


end AdaptiveCausalKernel
end OSSS
end StatMech
