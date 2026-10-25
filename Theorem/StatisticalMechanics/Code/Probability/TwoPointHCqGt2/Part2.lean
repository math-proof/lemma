/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.ConvexGapHC.Part2
import Def.StatisticalMechanics.Code.Probability.TwoPointHCqGt2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem hcq_smallDelta_of_lowRange {q : ℝ} (H : hcq_lowRangeResidue q) :
    cvg_smallDeltaResidue q := by
  intro p hp hp1 E _ _ _ φ hδ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδdef
  set q' : ℝ := 1 + (1 - u) / (4 * p * (1 - p)) with hq'
  have h4 : (0 : ℝ) < 4 * p * (1 - p) := by nlinarith
  
  have hrel : 1 - u = (q' - 1) * 4 * p * (1 - p) := by
    rw [hq']
    rw [show (1 + (1 - u) / (4 * p * (1 - p)) - 1) * 4 * p * (1 - p)
        = ((1 - u) / (4 * p * (1 - p))) * (4 * p * (1 - p)) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h4)]
  by_cases hcapped : 1 - 4 * p * (1 - p) ≤ u
  · 
    
    have hq1' : 1 ≤ q' := by
      rw [hq']
      have : 0 ≤ (1 - u) / (4 * p * (1 - p)) := div_nonneg (by linarith) h4.le
      linarith
    have hq2' : q' ≤ 2 := by
      rw [hq']
      have hsmall : (1 - u) / (4 * p * (1 - p)) ≤ 1 := by
        rw [div_le_one h4]; linarith
      linarith
    have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
    rcases eq_or_lt_of_le hδnn with hδ00 | hδ0
    · 
      
      
      have hupos : (0 : ℝ) < u / (2 - u) := by
        have h2u : (0 : ℝ) < 2 - u := by linarith
        positivity
      have hT0 : totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
        unfold totalInfl
        apply Finset.sum_eq_zero
        intro e _
        have hle : OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e ≤ δ := by
          rw [hδdef]; exact kkl_infl_le_maxInfl _ _ e
        have hge : 0 ≤ OSSS.infl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) e :=
          kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _ e
        rw [← hδ00] at hle; linarith
      rw [hT0, mul_zero]
      have hcap := frh_capped_martingale hp0 hp1 hq1' hq2'
        (by nlinarith [sq_nonneg (1 - 2*p)]) hu1.le hrel φ
      rw [← hδdef, hT0, mul_zero, mul_zero] at hcap
      exact hcap
    · 
      by_cases hthr : 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / q' - 1))
      · 
        exact hcq_star_capped_threshold hp0 hp1 φ hcapped hu1 hδ0 hq1' hq2' hrel hthr
      · 
        rw [not_le] at hthr
        exact H p hp hp1 φ hδ u hu0 hu1 (Or.inr hthr)
  · 
    rw [not_le] at hcapped
    exact H p hp hp1 φ hδ u hu0 hu1 (Or.inl hcapped)


theorem hcq_martingaleHC_of_lowRange {q : ℝ} (H : hcq_lowRangeResidue q) :
    mxd_martingaleHC_statement q :=
  cvg_martingaleHC_of_smallDelta (hcq_smallDelta_of_lowRange H)


theorem hcq_dominated_nonempty {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (_hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) :
    4 * (ptn_sigma p) ^ 2 ≤ δ ^ ((1 : ℝ) / (2 - 1) - (2 / (1 : ℝ) - 1)) := by
  have hgap : (1 : ℝ) / (2 - 1) - (2 / (1 : ℝ) - 1) = 0 := by norm_num
  rw [hgap, Real.rpow_zero]
  rw [ptn_sigma_sq hp0 hp1]
  nlinarith [sq_nonneg (1 - 2 * p)]


theorem hcq_threshold_of_gap_small {s δ g : ℝ} (hs0 : 0 < s)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hgle : g ≤ Real.log (1 / s) / Real.log (1 / δ)) :
    s ≤ δ ^ g := by
  have hlδ : 0 < Real.log (1 / δ) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hδ0]; linarith
  rw [Real.rpow_def_of_pos hδ0, show s = Real.exp (Real.log s) from (Real.exp_log hs0).symm]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (ne_of_gt hδ0), Real.log_one, zero_sub] at hgle hlδ
  rw [Real.log_div (by norm_num) (ne_of_gt hs0), Real.log_one, zero_sub] at hgle
  rw [le_div_iff₀ hlδ] at hgle
  nlinarith [hgle, mul_comm g (Real.log δ)]


theorem hcq_residue_proper {p δ : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ u : ℝ, (0 < u ∧ u < 1) ∧ 1 - 4 * p * (1 - p) ≤ u ∧
      4 * (ptn_sigma p) ^ 2
        ≤ δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1)) := by
  have hp0 : 0 < p := by linarith
  set s := 4 * p * (1 - p) with hsdef
  have hsval : (ptn_sigma p) ^ 2 = p * (1 - p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p) ^ 2 = s := by rw [hsval, hsdef]; ring
  have hs0 : 0 < s := by rw [hsdef]; nlinarith
  have hs1 : s < 1 := by
    rw [hsdef]
    have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
    have hpos : 0 < (1 - 2 * p) ^ 2 := by positivity
    nlinarith [hpos]
  
  set B := Real.log (1 / s) / Real.log (1 / δ) with hBdef
  have hlδ : 0 < Real.log (1 / δ) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hδ0]; linarith
  have hls : 0 < Real.log (1 / s) := by
    rw [Real.log_pos_iff (by positivity)]; rw [lt_div_iff₀ hs0]; linarith
  have hB : 0 < B := by rw [hBdef]; positivity
  
  have h1s : 0 < 1 - s := by linarith
  set m := min s (B * s / (2 * (1 - s))) with hm
  have hmpos : 0 < m := by rw [hm]; apply lt_min hs0; positivity
  have hms_s : m ≤ s := min_le_left _ _
  have hms_B : m ≤ B * s / (2 * (1 - s)) := min_le_right _ _
  set t := m / 2 with htdef
  have htpos : 0 < t := by positivity
  have hts : t < s := by rw [htdef]; linarith [hmpos]
  set u := 1 - t with hudef
  refine ⟨u, ⟨by rw [hudef]; linarith [hts, hs1], by rw [hudef]; linarith⟩, ?_, ?_⟩
  · rw [hudef]; linarith [hts]
  · 
    rw [h4σ]
    have hu_lo : 1 - s < u := by rw [hudef]; linarith [hts]
    have hu_hi : u < 1 := by rw [hudef]; linarith
    have hgapbd : u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ 2 * (1 - u) * (1 - s) / s :=
      hcq_gap_le hs0 hs1 hu_lo hu_hi
    have h1u_eq : 1 - u = t := by rw [hudef]; ring
    have hgleB : 2 * (1 - u) * (1 - s) / s ≤ B := by
      rw [h1u_eq, div_le_iff₀ hs0]
      have hstep : (B * s / (2 * (1 - s))) * (1 - s) = B * s / 2 := by field_simp
      calc 2 * t * (1 - s) = (2 * t) * (1 - s) := by ring
        _ ≤ (2 * (B * s / (2 * (1 - s)))) * (1 - s) :=
            mul_le_mul_of_nonneg_right (by linarith [hms_B]) h1s.le
        _ = 2 * (B * s / 2) := by rw [mul_assoc, hstep]
        _ = B * s := by ring
    have hgle : u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ B := le_trans hgapbd hgleB
    rw [hBdef] at hgle
    exact hcq_threshold_of_gap_small hs0 hδ0 hδ1 hgle


theorem hcq_antecedent_not_tautology {p δ : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ u : ℝ, (0 < u ∧ u < 1) ∧
      ¬ (u < 1 - 4 * p * (1 - p) ∨
          δ ^ (u / (2 - u) - (2 / (1 + (1 - u) / (4 * p * (1 - p))) - 1))
            < 4 * (ptn_sigma p) ^ 2) := by
  obtain ⟨u, hu, hcap, hthr⟩ := hcq_residue_proper hp hp1 hδ0 hδ1
  refine ⟨u, hu, ?_⟩
  rintro (hlow | hbad)
  · linarith [hcap]
  · linarith [hthr]


theorem hcq_lowRange_nonvacuous {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    {u : ℝ} (_hu0 : 0 < u) (_hu1 : u < 1) :
    (0 : ℝ)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  apply mul_nonneg
  · exact Real.rpow_nonneg
      (kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _) _
  · exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _

end StatMech.Probability
