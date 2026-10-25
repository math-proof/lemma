/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MasterFamilyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VarGapProve2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTwoPoint.Part3
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem mfp_chord_bound {G : ℝ → ℝ} (hG : ConvexOn ℝ (Icc (0:ℝ) 1) G) {u anc : ℝ}
    (ha0 : 0 < anc) (ha1 : anc ≤ 1) (hu0 : 0 ≤ u) (hua : u ≤ anc) :
    G u ≤ (1 - u / anc) * G 0 + (u / anc) * G anc := by
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hmema : anc ∈ Icc (0:ℝ) 1 := ⟨ha0.le, ha1⟩
  have hr0 : (0:ℝ) ≤ u / anc := by positivity
  have hr1 : u / anc ≤ 1 := by rw [div_le_one ha0]; exact hua
  have hkey := hG.2 hmem0 hmema (by linarith : (0:ℝ) ≤ 1 - u / anc) hr0
    (by ring : (1 - u / anc) + u / anc = 1)
  have heq : (1 - u / anc) • (0:ℝ) + (u / anc) • anc = u := by
    simp only [smul_eq_mul, mul_zero, zero_add]; field_simp
  rw [heq] at hkey
  simpa only [smul_eq_mul] using hkey


theorem mfp_L_chord_bound [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - u) ^ (S.card - 1)
        * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)
      ≤ ((1 - u) + u * (maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)))
        * totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) := by
  set f := fun ω => if φ ω then (1 : ℝ) else 0 with hf
  set δ := maxInfl (OSSS.bernoulliWeight p) f with hδ
  set T := totalInfl (OSSS.bernoulliWeight p) f with hT
  set Lf := fun v : ℝ => ∑ S : Finset ι, 4 * (S.card : ℝ) * (1 - v) ^ (S.card - 1)
    * (ptn_coeff p f S) ^ 2 with hLf
  have hLconv : ConvexOn ℝ (Icc (0:ℝ) 1) Lf := cvg_L_convexOn p φ
  
  have hL0 : Lf 0 ≤ T := frh_at_zero hp0 hp1 φ
  have hδnn : 0 ≤ δ := kkl_maxInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hTnn : 0 ≤ T := kkl_totalInfl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f
  have hL1 : Lf 1 ≤ δ * T := by
    have hbnd := frh_endpoint_one hp0 hp1 φ
    rw [show δ ^ ((1:ℝ) / (2 - 1)) = δ by rw [show (1:ℝ)/(2-1) = 1 by norm_num, Real.rpow_one]] at hbnd
    exact hbnd
  
  have hchord := mfp_chord_bound hLconv (anc := 1) (by norm_num) (le_refl _) hu0 hu1
  rw [div_one] at hchord
  
  calc Lf u ≤ (1 - u) * Lf 0 + u * Lf 1 := hchord
    _ ≤ (1 - u) * T + u * (δ * T) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hL0 (by linarith)
        · exact mul_le_mul_of_nonneg_left hL1 hu0
    _ = ((1 - u) + u * δ) * T := by ring


theorem mfp_chord_route_dead {T : ℝ} (hT : 0 < T) :
    Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T
      < (1 - (1:ℝ) / 2) * T := by
  
  have hR : Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) = Real.exp (-1) := by
    rw [← Real.exp_mul]; congr 1; norm_num
  rw [hR]
  
  have hkey : Real.exp (-1) < 1 - (1:ℝ) / 2 := by
    rw [Real.exp_neg, show (1:ℝ) - 1 / 2 = (2:ℝ)⁻¹ by norm_num,
      inv_lt_inv₀ (by positivity) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  exact (mul_lt_mul_of_pos_right hkey hT)


theorem mfp_chord_gap_pos {T : ℝ} (hT : 0 < T) :
    0 < (1 - (1:ℝ) / 2) * T - Real.exp (-3) ^ (((1:ℝ) / 2) / (2 - 1 / 2)) * T := by
  have := mfp_chord_route_dead hT
  linarith


end StatMech.Probability
