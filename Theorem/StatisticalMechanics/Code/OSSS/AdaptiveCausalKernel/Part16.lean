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
import Def.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part16
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


lemma volume_thresholdInterval (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (b : Bool) :
    (volume (thresholdInterval q b)).toReal = bitWeight q b := by
  cases b <;> simp [thresholdInterval, bitWeight, Real.volume_Ico, hq0, hq1]


lemma volume_inter_threshold_false_add_true (A : Set ℝ) (hA : MeasurableSet A)
    (hAcube : A ⊆ Set.Ico (0 : ℝ) 1) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (volume (A ∩ thresholdInterval q false)).toReal +
      (volume (A ∩ thresholdInterval q true)).toReal = (volume A).toReal := by
  have hd : Disjoint (A ∩ thresholdInterval q false) (A ∩ thresholdInterval q true) := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    exact (not_lt_of_ge hx1.2.1) hx0.2.2
  have hu : (A ∩ thresholdInterval q false) ∪ (A ∩ thresholdInterval q true) = A := by
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      by_cases h : x < q
      · left
        exact ⟨hx, by simpa [thresholdInterval] using ⟨hAcube hx |>.1, h⟩⟩
      · right
        exact ⟨hx, by simpa [thresholdInterval] using ⟨le_of_not_gt h, hAcube hx |>.2⟩⟩
  have hIt : MeasurableSet (thresholdInterval q true) := by
    simp [thresholdInterval]
  have hm := measure_union (μ := volume) hd (hA.inter hIt)
  rw [hu] at hm
  have hAfin : volume A < ⊤ := by
    calc
      volume A ≤ volume (Set.Ico (0 : ℝ) 1) := measure_mono hAcube
      _ < ⊤ := by simp [Real.volume_Ico]
  have h0 : volume (A ∩ thresholdInterval q false) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hAfin)
  have h1 : volume (A ∩ thresholdInterval q true) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hAfin)
  rw [← ENNReal.toReal_add h0 h1, ← hm]


lemma volume_thresholdInterval_inter (a q : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (base target : Bool) :
    (volume (thresholdInterval a base ∩ thresholdInterval q target)).toReal =
      overlapWeight a q base target := by
  cases base <;> cases target <;>
    simp only [thresholdInterval, Bool.false_eq_true, if_false, if_true,
      Set.Ico_inter_Ico, Real.volume_Ico]
  · rw [max_self, min_def, overlapWeight]
    by_cases h : a ≤ q
    · rw [if_pos h, sub_zero, ENNReal.toReal_ofReal ha0, min_eq_left h]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [if_neg h, sub_zero, ENNReal.toReal_ofReal hq0, min_eq_right hqa]
  · rw [max_eq_right hq0, min_eq_left ha1, overlapWeight]
    by_cases h : a ≤ q
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr h), ENNReal.toReal_zero,
        max_eq_right (sub_nonpos.mpr h)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hqa), max_eq_left (sub_nonneg.mpr hqa)]
  · rw [max_eq_left ha0, min_eq_right hq1, overlapWeight]
    by_cases h : a ≤ q
    · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h), max_eq_left (sub_nonneg.mpr h)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr hqa), ENNReal.toReal_zero,
        max_eq_right (sub_nonpos.mpr hqa)]
  · rw [min_self, overlapWeight]
    by_cases h : a ≤ q
    · rw [max_eq_right h, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)]
    · have hqa : q ≤ a := le_of_not_ge h
      rw [max_eq_left hqa, ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)]


lemma rawInterval_inter_toReal_eq_overlapWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega) {n : ℕ} (sigma : Fin n → E)
    (base target : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma base i ∩
        GrandCoupling.rawInterval mu sigma target i)).toReal =
      overlapWeight (thr mu sigma base i) (thr mu sigma target i)
        (base (sigma i)) (target (sigma i)) := by
  have ha := thr_mem_Icc mu hpos sigma base i
  have hq := thr_mem_Icc mu hpos sigma target i
  rw [Measure.restrict_apply' measurableSet_Icc]
  have hae :
      (fun z : ℝ => z ∈
        (GrandCoupling.rawInterval mu sigma base i ∩
          GrandCoupling.rawInterval mu sigma target i) ∩ Set.Icc (0 : ℝ) 1)
        =ᵐ[volume]
      (fun z : ℝ => z ∈
        thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
          thresholdInterval (thr mu sigma target i) (target (sigma i))) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    cases hb : base (sigma i) <;> cases ht : target (sigma i) <;>
      simp only [GrandCoupling.rawInterval, hb, ht, Bool.false_eq_true, if_false, if_true,
        thresholdInterval, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_Icc,
        Set.mem_Ico]
    all_goals
      apply propext
      constructor
      · rintro ⟨⟨hB, hT⟩, h0, h1⟩
        have hzlt : z < 1 := lt_of_le_of_ne h1 hz1
        constructor <;> constructor <;> linarith
      · rintro ⟨⟨hB0, hB1⟩, hT0, hT1⟩
        exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hm := measure_congr hae
  change volume
    ((GrandCoupling.rawInterval mu sigma base i ∩
      GrandCoupling.rawInterval mu sigma target i) ∩ Set.Icc (0 : ℝ) 1) =
    volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
      thresholdInterval (thr mu sigma target i) (target (sigma i))) at hm
  rw [hm]
  exact volume_thresholdInterval_inter _ _ ha.1 ha.2 hq.1 hq.2 _ _

lemma rawInterval_tripleInter_toReal_eq_tripleOverlapWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    {n : ℕ} (sigma : Fin n → E) (base left right : ConfigSpace E) (i : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)
      (GrandCoupling.rawInterval mu sigma base i ∩
        GrandCoupling.rawInterval mu sigma left i ∩
        GrandCoupling.rawInterval mu sigma right i)).toReal =
      (volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
        thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
        thresholdInterval (thr mu sigma right i) (right (sigma i)))).toReal := by
  rw [Measure.restrict_apply' measurableSet_Icc]
  have hae :
      (fun z : ℝ => z ∈
        (GrandCoupling.rawInterval mu sigma base i ∩
          GrandCoupling.rawInterval mu sigma left i ∩
          GrandCoupling.rawInterval mu sigma right i) ∩ Set.Icc (0 : ℝ) 1)
        =ᵐ[volume]
      (fun z : ℝ => z ∈
        thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
          thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
          thresholdInterval (thr mu sigma right i) (right (sigma i))) := by
    filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with z hz
    have hz1 : z ≠ 1 := by simpa using hz
    have ha := thr_mem_Icc mu hpos sigma base i
    have hq := thr_mem_Icc mu hpos sigma left i
    have hr := thr_mem_Icc mu hpos sigma right i
    cases hb : base (sigma i) <;> cases hl : left (sigma i) <;>
      cases hh : right (sigma i) <;>
      simp only [GrandCoupling.rawInterval, hb, hl, hh, Bool.false_eq_true,
        if_false, if_true, thresholdInterval, Set.mem_inter_iff, Set.mem_Iio,
        Set.mem_Ici, Set.mem_Icc, Set.mem_Ico]
    all_goals
      apply propext
      constructor
      · rintro ⟨⟨⟨hB, hL⟩, hR⟩, h0, h1⟩
        have hzlt : z < 1 := lt_of_le_of_ne h1 hz1
        constructor
        · constructor <;> constructor <;> linarith
        · constructor <;> linarith
      · rintro ⟨⟨⟨hB0, hB1⟩, hL0, hL1⟩, hR0, hR1⟩
        exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩,
          by linarith, by linarith⟩
  have hm := measure_congr hae
  change volume
    ((GrandCoupling.rawInterval mu sigma base i ∩
      GrandCoupling.rawInterval mu sigma left i ∩
      GrandCoupling.rawInterval mu sigma right i) ∩ Set.Icc (0 : ℝ) 1) =
    volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩
      thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩
      thresholdInterval (thr mu sigma right i) (right (sigma i))) at hm
  rw [hm]


lemma frozenRawPair_toReal_eq_splitWeight (mu : ConfigSpace E → ℝ)
    (hpos : ∀ omega, 0 < mu omega)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) (i : Fin (Fintype.card E)) :
    (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (frozenRawPair mu S base target i)).toReal =
      splitWeight (independentAt S base (realizedEquiv S base i))
        (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
        (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
        (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  let sigma := realizedEquiv S base
  have hsigma : realizedEquiv S base = sigma := rfl
  unfold frozenRawPair
  simp only [hsigma]
  by_cases hi : independentAt S base (sigma i)
  · rw [if_pos hi, Measure.prod_prod, ENNReal.toReal_mul,
      rawInterval_toReal_eq_bitWeight mu hpos,
      rawInterval_toReal_eq_bitWeight mu hpos]
    simp [splitWeight, independentWeight, hi]
  · rw [if_neg hi, Measure.prod_prod, ENNReal.toReal_mul,
      rawInterval_inter_toReal_eq_overlapWeight mu hpos]
    simp [splitWeight, hi]


theorem pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight
    (mu : ConfigSpace E → ℝ) (hpos : ∀ omega, 0 < mu omega)
    (S : CausalOrder (Finset.univ : Finset E))
    (base target : ConfigSpace E) :
    (pairedCube (Fintype.card E) (frozenCodeAtom mu S base target)).toReal =
      ∏ i : Fin (Fintype.card E),
        splitWeight (independentAt S base (realizedEquiv S base i))
          (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i)
          (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i)
          (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
  rw [pairedCube_frozenCodeAtom, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact frozenRawPair_toReal_eq_splitWeight mu hpos S base target i

lemma overlapWeight_sum_base (a q : ℝ) (target : Bool) :
    overlapWeight a q false target + overlapWeight a q true target =
      if target then 1 - q else q := by
  cases target with
  | false =>
      simp only [overlapWeight, Bool.false_eq_true, if_false]
      by_cases h : a ≤ q
      · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
        ring
      · have hqa : q ≤ a := le_of_not_ge h
        rw [min_eq_right hqa, max_eq_right (sub_nonpos.mpr hqa)]
        ring
  | true =>
      simp only [overlapWeight, if_true]
      by_cases h : a ≤ q
      · rw [max_eq_right (sub_nonpos.mpr h), max_eq_right h]
        ring
      · have hqa : q ≤ a := le_of_not_ge h
        rw [max_eq_left (sub_nonneg.mpr hqa), max_eq_left hqa]
        ring

lemma overlapWeight_same_threshold_ne (q : ℝ) {b c : Bool} (hbc : b ≠ c) :
    overlapWeight q q b c = 0 := by
  cases b <;> cases c <;> simp_all [overlapWeight]

lemma splitWeight_sum_base (independent : Bool) (a q : ℝ) (target : Bool) :
    splitWeight independent a q false target + splitWeight independent a q true target =
      bitWeight q target := by
  cases independent with
  | false =>
      simp only [splitWeight, Bool.false_eq_true, if_false]
      rw [overlapWeight_sum_base]
      cases target <;> simp [bitWeight]
  | true =>
      simp only [splitWeight, if_true]
      exact independentWeight_sum_base a q target

lemma overlapWeight_comm (a q : ℝ) (b c : Bool) :
    overlapWeight a q b c = overlapWeight q a c b := by
  cases b <;> cases c <;> simp [overlapWeight, min_comm, max_comm]

end AdaptiveCausalKernel
end OSSS
end StatMech
