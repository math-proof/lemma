/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/TwoPointHCqGt2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.ConvexGapHC.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem hcq_exponent_le {p q' u : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hu1 : u < 1) (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p)) :
    2 / q' - 1 ≤ u / (2 - u) := by
  have h4 : 0 < 4 * p * (1 - p) := by nlinarith
  have h4le : 4 * p * (1 - p) ≤ 1 := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hq1 : 1 ≤ q' := by nlinarith
  have h2u : 0 < 2 - u := by linarith
  
  have hge : 2 - u ≤ q' := by
    have hgeqm1 : 1 - u ≤ q' - 1 := by rw [hrel]; nlinarith [hq1]
    linarith
  have hdiv : 2 / q' ≤ 2 / (2 - u) := div_le_div_of_nonneg_left (by norm_num) h2u hge
  have htgt : 2 / (2 - u) - 1 = u / (2 - u) := by field_simp; ring
  linarith [hdiv, htgt]


theorem hcq_gap_closedForm {s u : ℝ} (hs0 : 0 < s) (hu1 : u < 1) (hslu : 0 < s + 1 - u) :
    u / (2 - u) - (2 / (1 + (1 - u) / s) - 1)
      = 2 * (1 - u) * (1 - s) / ((s + 1 - u) * (2 - u)) := by
  have h2u : 0 < 2 - u := by linarith
  have hrw : (1 : ℝ) + (1 - u) / s = (s + 1 - u) / s := by field_simp; ring
  rw [hrw, div_div_eq_mul_div, div_sub_one (ne_of_gt hslu)]
  field_simp
  ring


theorem hcq_gap_le {s u : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hu_lo : 1 - s < u) (hu_hi : u < 1) :
    u / (2 - u) - (2 / (1 + (1 - u) / s) - 1) ≤ 2 * (1 - u) * (1 - s) / s := by
  have hslu : 0 < s + 1 - u := by linarith
  rw [hcq_gap_closedForm hs0 hu_hi hslu]
  have h1u : 0 < 1 - u := by linarith
  have h1s : 0 < 1 - s := by linarith
  apply div_le_div_of_nonneg_left (by positivity) hs0
  nlinarith [h1u, h1s]


theorem hcq_capped_full [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1) :
    ∃ q' : ℝ, 1 ≤ q' ∧ q' ≤ 2 ∧ 1 - u = (q' - 1) * 4 * p * (1 - p) ∧
      (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
        ≤ 4 * (ptn_sigma p) ^ 2
          * ((maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
            * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) := by
  obtain ⟨q', hq1, hq2, hrel⟩ := frh_capped_param hp0 hp1 hlo hu1
  refine ⟨q', hq1, hq2, hrel, ?_⟩
  have hu0 : 0 ≤ u := by nlinarith [sq_nonneg (1 - 2 * p)]
  exact frh_capped_martingale hp0 hp1 hq1 hq2 hu0 hu1 hrel φ


theorem hcq_dom_of_threshold {p δ q' u : ℝ} (hδ0 : 0 < δ)
    (hthr : 4 * (ptn_sigma p) ^ 2 ≤ δ ^ (u / (2 - u) - (2 / q' - 1))) :
    4 * (ptn_sigma p) ^ 2 * δ ^ (2 / q' - 1) ≤ δ ^ (u / (2 - u)) := by
  have key : δ ^ (u / (2 - u)) = δ ^ (u / (2 - u) - (2 / q' - 1)) * δ ^ (2 / q' - 1) := by
    rw [← Real.rpow_add hδ0]; congr 1; ring
  rw [key]
  exact mul_le_mul_of_nonneg_right hthr (Real.rpow_nonneg hδ0.le _)


theorem hcq_star_of_dominates [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u ≤ 1)
    {q' : ℝ} (hq1 : 1 ≤ q') (hq2 : q' ≤ 2)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
    (hdom : 4 * (ptn_sigma p) ^ 2
        * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (2 / q' - 1)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hu0 : 0 ≤ u := by nlinarith [sq_nonneg (1 - 2 * p)]
  have hcap := frh_capped_martingale hp0 hp1 hq1 hq2 hu0 hu1 hrel φ
  set δ := maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) with hT
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) _
  calc (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
          * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ 4 * (ptn_sigma p) ^ 2 * (δ ^ (2 / q' - 1) * T) := hcap
    _ = (4 * (ptn_sigma p) ^ 2 * δ ^ (2 / q' - 1)) * T := by ring
    _ ≤ δ ^ (u / (2 - u)) * T := mul_le_mul_of_nonneg_right hdom hTnn


theorem hcq_star_capped_threshold [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ}
    (hlo : 1 - 4 * p * (1 - p) ≤ u) (hu1 : u < 1)
    (hδ0 : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    {q' : ℝ} (hq1 : 1 ≤ q') (hq2 : q' ≤ 2)
    (hrel : 1 - u = (q' - 1) * 4 * p * (1 - p))
    (hthr : 4 * (ptn_sigma p) ^ 2
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u) - (2 / q' - 1))) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hdom := hcq_dom_of_threshold hδ0 hthr
  exact hcq_star_of_dominates hp0 hp1 φ hlo hu1.le hq1 hq2 hrel hdom


theorem hcq_smallDelta_p_half [Nonempty ι]
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff (1 / 2 : ℝ) (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0))
          ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hp0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) < 1 := by norm_num
  
  have h4σ : (4 : ℝ) * (ptn_sigma (1 / 2 : ℝ)) ^ 2 = 1 := by
    rw [ptn_sigma_sq hp0 hp1]; norm_num
  have hlo : 1 - 4 * (1 / 2 : ℝ) * (1 - 1 / 2) ≤ u := by norm_num; linarith [hu0]
  
  set q' : ℝ := 2 - u with hq'
  have hq1 : 1 ≤ q' := by rw [hq']; linarith
  have hq2 : q' ≤ 2 := by rw [hq']; linarith
  have hrel : 1 - u = (q' - 1) * 4 * (1 / 2 : ℝ) * (1 - 1 / 2) := by rw [hq']; ring
  
  have h2u0 : (2 : ℝ) - u ≠ 0 := by intro h; linarith
  have hgap : u / (2 - u) - (2 / q' - 1) = 0 := by
    rw [hq', sub_eq_zero, div_sub_one h2u0]
    congr 1; ring
  have hδ0 : 0 < maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
      ∨ maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
    rcases eq_or_lt_of_le (kkl_maxInfl_nonneg
      (OSSS.bernoulliWeight_isProbWeight (E := ι) hp0.le hp1.le) _) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hδ0 with hδpos | hδzero
  · 
    apply hcq_star_capped_threshold hp0 hp1 φ hlo hu1 hδpos hq1 hq2 hrel
    rw [hgap, Real.rpow_zero, h4σ]
  · 
    have hcap := frh_capped_martingale hp0 hp1 hq1 hq2 (by linarith [hu0]) hu1.le hrel φ
    rw [hδzero] at hcap ⊢
    have hupos : u / (2 - u) ≠ 0 := by
      have h2u : (0 : ℝ) < 2 - u := by linarith
      positivity
    rw [Real.zero_rpow hupos, zero_mul]
    rw [Real.zero_rpow (by
      have : (2 : ℝ) / q' - 1 = u / (2 - u) := by
        rw [hq', div_sub_one h2u0]; congr 1; ring
      rw [this]; exact hupos)] at hcap
    simpa using hcap


end StatMech.Probability
