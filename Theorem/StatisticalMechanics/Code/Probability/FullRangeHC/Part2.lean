/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FullRangeHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part11
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Theorem.StatisticalMechanics.Code.Probability.MaxElementDecomp.Part5
import Def.StatisticalMechanics.Code.Probability.FullRangeHC.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem frh_endpoint_one [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - (1:ℝ)) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ ((1:ℝ) / (2 - 1))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  have hcap := frh_capped_martingale hp0 hp1 (le_refl (1:ℝ)) (by norm_num : (1:ℝ) ≤ 2)
    (by norm_num : (0:ℝ) ≤ 1) (le_refl (1:ℝ)) (by ring) φ
  
  have hδnn : 0 ≤ δ := by rw [hδ]; exact kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := by rw [hT]; exact kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hσ2val : (ptn_sigma p)^2 = p*(1-p) := ptn_sigma_sq hp0 hp1
  have h4σ : 4 * (ptn_sigma p)^2 ≤ 1 := by rw [hσ2val]; nlinarith [sq_nonneg (1 - 2*p)]
  have hσnn : (0:ℝ) ≤ 4 * (ptn_sigma p)^2 := by positivity
  have hexp1 : (2:ℝ) / 1 - 1 = (1:ℝ) / (2 - 1) := by norm_num
  have hRHSnn : 0 ≤ δ ^ ((2:ℝ)/1 - 1) * T := by positivity
  refine le_trans hcap ?_
  calc 4 * (ptn_sigma p)^2 * (δ ^ ((2:ℝ)/1 - 1) * T)
      ≤ 1 * (δ ^ ((2:ℝ)/1 - 1) * T) := mul_le_mul_of_nonneg_right h4σ hRHSnn
    _ = δ ^ ((2:ℝ)/1 - 1) * T := by rw [one_mul]
    _ = δ ^ ((1:ℝ) / (2 - 1)) * T := by rw [hexp1]


theorem frh_martingaleHC_of_openResidue {q : ℝ} (H : frh_openResidue q) :
    mxd_martingaleHC_statement q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  rcases eq_or_lt_of_le hu0 with hu0' | hu0'
  · 
    subst hu0'
    have hbnd := frh_at_zero hp0 hp1 φ
    rw [show (0:ℝ) / (2 - 0) = 0 by norm_num, Real.rpow_zero, one_mul]
    exact hbnd
  · 
    rcases eq_or_lt_of_le hu1 with hu1' | hu1'
    · 
      subst hu1'
      exact frh_endpoint_one hp0 hp1 φ
    · 
      exact H p hp hp1 φ u hu0' hu1'


theorem frh_lowNoise_range_nonempty {p : ℝ} (hp : 1 / 2 < p) (_hp1 : p < 1) :
    0 < 1 - 4 * p * (1 - p) := by
  have heq : 1 - 4 * p * (1 - p) = (1 - 2 * p) ^ 2 := by ring
  rw [heq]
  have hne : (1 - 2 * p) ≠ 0 := by intro h; nlinarith [h]
  positivity


theorem frh_openResidue_c0 {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (u : ℝ) :
    (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) ^ (u / (2 - u))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  have hzero : (∑ S : Finset E, (0 : ℝ) * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
      * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2) = 0 := by
    apply Finset.sum_eq_zero; intro S _; ring
  rw [hzero]
  have hδnn : 0 ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  have hTnn : 0 ≤ totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
    kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0 hp1) _
  positivity

end StatMech.Probability
