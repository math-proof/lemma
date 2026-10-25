/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part5


namespace StatMech.Onsager

theorem ons_criticalParameterNeighborhood_mem_nhds :
    ons_criticalParameterNeighborhood ∈ nhds ons_betaC := by
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcosh : Continuous (fun b : ℝ => Real.cosh (2 * b)) :=
    Real.continuous_cosh.comp hlin
  have hsinhEv : ∀ᶠ b : ℝ in nhds ons_betaC,
      (1 / 2 : ℝ) < Real.sinh (2 * b) := by
    apply continuousAt_const.eventually_lt hsinh.continuousAt
    rw [ons_betaC_sinh]
    norm_num
  have hcoshCrit : |Real.cosh (2 * ons_betaC)| < 2 := by
    rw [abs_of_pos (Real.cosh_pos _)]
    have hsq := ons_cosh_betaC_sq
    nlinarith [Real.cosh_pos (2 * ons_betaC)]
  have hcoshEv : ∀ᶠ b : ℝ in nhds ons_betaC,
      |Real.cosh (2 * b)| < 2 := by
    exact hcosh.abs.continuousAt.eventually_lt continuousAt_const hcoshCrit
  filter_upwards [hsinhEv, hcoshEv] with b hs hc
  exact ⟨hs, hc⟩

theorem ons_gInt_lower_criticalNeighborhood {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    (Real.sinh (2 * b) - 1) ^ 2 +
        (2 - Real.cos k1 - Real.cos k2) / 4 ≤ ons_gInt b k1 k2 := by
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  rw [ons_gInt_decompose]
  have hs : 1 / 2 ≤ Real.sinh (2 * b) := hb.1.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) hA]

theorem ons_gIntBetaDeriv_abs_le_criticalNeighborhood {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood) :
    |ons_gIntBetaDeriv b k1 k2| ≤
      4 * (2 * |Real.sinh (2 * b) - 1| +
        (2 - Real.cos k1 - Real.cos k2)) := by
  have hA : 0 ≤ 2 - Real.cos k1 - Real.cos k2 := by
    linarith [Real.cos_le_one k1, Real.cos_le_one k2]
  have hid : 2 * Real.sinh (2 * b) - Real.cos k1 - Real.cos k2 =
      2 * (Real.sinh (2 * b) - 1) +
        (2 - Real.cos k1 - Real.cos k2) := by ring
  rw [ons_gIntBetaDeriv, abs_mul, abs_mul, hid]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hinner : |2 * (Real.sinh (2 * b) - 1) +
      (2 - Real.cos k1 - Real.cos k2)| ≤
      2 * |Real.sinh (2 * b) - 1| +
        (2 - Real.cos k1 - Real.cos k2) := by
    calc
      _ ≤ |2 * (Real.sinh (2 * b) - 1)| +
          |2 - Real.cos k1 - Real.cos k2| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hA]
  have hc : |Real.cosh (2 * b)| ≤ 2 := hb.2.le
  nlinarith [mul_le_mul hc hinner (abs_nonneg _)
    (show 0 ≤ (2 : ℝ) from zero_le_two)]

theorem ons_delta_ratio_le_inv_sqrt {delta A : ℝ} (hA : 0 < A) :
    (2 * |delta| + A) / (delta ^ 2 + A) ≤ 1 / Real.sqrt A + 1 := by
  have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hsqrtSq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA.le
  have hden : 0 < delta ^ 2 + A := by positivity
  have hamgm : 2 * |delta| * Real.sqrt A ≤ delta ^ 2 + A := by
    nlinarith [sq_nonneg (|delta| - Real.sqrt A), sq_abs delta]
  rw [div_le_iff₀ hden]
  have hscaled : 2 * |delta| ≤ (delta ^ 2 + A) / Real.sqrt A := by
    exact (le_div_iff₀ hsqrt).2 (by simpa [mul_assoc] using hamgm)
  calc
    2 * |delta| + A ≤
        (delta ^ 2 + A) / Real.sqrt A + (delta ^ 2 + A) := by
          gcongr
          exact le_add_of_nonneg_left (sq_nonneg delta)
    _ = (1 / Real.sqrt A + 1) * (delta ^ 2 + A) := by ring

theorem ons_delta_ratio_quarter_le_inv_sqrt {delta A : ℝ} (hA : 0 < A) :
    (2 * |delta| + A) / (delta ^ 2 + A / 4) ≤
      8 * (1 / Real.sqrt A + 1) := by
  have hquarter : 0 < A / 4 := by positivity
  have hden : 0 < delta ^ 2 + A / 4 := by positivity
  have hbase := ons_delta_ratio_le_inv_sqrt (delta := delta) hquarter
  have hnum : 2 * |delta| + A ≤ 4 * (2 * |delta| + A / 4) := by
    nlinarith [abs_nonneg delta]
  calc
    (2 * |delta| + A) / (delta ^ 2 + A / 4) ≤
        4 * ((2 * |delta| + A / 4) / (delta ^ 2 + A / 4)) := by
          rw [← mul_div_assoc]
          exact (div_le_div_iff_of_pos_right hden).2 hnum
    _ ≤ 4 * (1 / Real.sqrt (A / 4) + 1) := by gcongr
    _ = 4 * (2 / Real.sqrt A + 1) := by
      rw [Real.sqrt_div (le_of_lt hA)]
      norm_num
    _ ≤ 8 * (1 / Real.sqrt A + 1) := by
      have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
      field_simp
      nlinarith

theorem ons_logGIntBetaDeriv_abs_le_criticalA {b k1 k2 : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hA : 0 < 2 - Real.cos k1 - Real.cos k2) :
    |ons_logGIntBetaDeriv b k1 k2| ≤
      32 * (1 / Real.sqrt (2 - Real.cos k1 - Real.cos k2) + 1) := by
  let A : ℝ := 2 - Real.cos k1 - Real.cos k2
  let delta : ℝ := Real.sinh (2 * b) - 1
  have hden0 : 0 < delta ^ 2 + A / 4 := by dsimp [A]; positivity
  have hgLower : delta ^ 2 + A / 4 ≤ ons_gInt b k1 k2 := by
    simpa only [A, delta] using ons_gInt_lower_criticalNeighborhood hb
  have hgPos : 0 < ons_gInt b k1 k2 := hden0.trans_le hgLower
  have hnum := ons_gIntBetaDeriv_abs_le_criticalNeighborhood
    (k1 := k1) (k2 := k2) hb
  change |ons_gIntBetaDeriv b k1 k2 / ons_gInt b k1 k2| ≤ _
  rw [abs_div, abs_of_pos hgPos]
  calc
    |ons_gIntBetaDeriv b k1 k2| / ons_gInt b k1 k2 ≤
        (4 * (2 * |delta| + A)) / (delta ^ 2 + A / 4) := by
          apply div_le_div₀
          · positivity
          · simpa only [A, delta] using hnum
          · exact hden0
          · exact hgLower
    _ = 4 * ((2 * |delta| + A) / (delta ^ 2 + A / 4)) := by ring
    _ ≤ 4 * (8 * (1 / Real.sqrt A + 1)) := by
      gcongr
      exact ons_delta_ratio_quarter_le_inv_sqrt (by simpa only [A] using hA)
    _ = 32 * (1 / Real.sqrt A + 1) := by
      ring
    _ = 32 * (1 / Real.sqrt (2 - Real.cos k1 - Real.cos k2) + 1) := by
      rfl

theorem ons_criticalDenom_lower_abs_mul {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi) :
    |x * y| / Real.pi ^ 2 ≤ 2 - Real.cos x - Real.cos y := by
  have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hxabs : |x| ≤ Real.pi := abs_le.mpr hx
  have hyabs : |y| ≤ Real.pi := abs_le.mpr hy
  have hxcos := Real.cos_le_one_sub_mul_cos_sq hxabs
  have hycos := Real.cos_le_one_sub_mul_cos_sq hyabs
  have hxquad : 2 * x ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos x) := by
    have hdiv : (2 * x ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos x := by
      convert (show 2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x by linarith) using 1
      all_goals ring
    have h := (div_le_iff₀ hpSq).mp hdiv
    nlinarith
  have hyquad : 2 * y ^ 2 ≤ Real.pi ^ 2 * (1 - Real.cos y) := by
    have hdiv : (2 * y ^ 2) / Real.pi ^ 2 ≤ 1 - Real.cos y := by
      convert (show 2 / Real.pi ^ 2 * y ^ 2 ≤ 1 - Real.cos y by linarith) using 1
      all_goals ring
    have h := (div_le_iff₀ hpSq).mp hdiv
    nlinarith
  have habs : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  apply (div_le_iff₀ hpSq).2
  nlinarith

theorem ons_inv_sqrt_criticalDenom_le_product {x y : ℝ}
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
      Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) := by
  have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
  have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hA := ons_criticalDenom_lower_abs_mul hx hy
  have hApos : 0 < 2 - Real.cos x - Real.cos y :=
    (div_pos hxy hpSq).trans_le hA
  have hsA : 0 < Real.sqrt (2 - Real.cos x - Real.cos y) := Real.sqrt_pos.2 hApos
  have hsxy : 0 < Real.sqrt |x * y| := Real.sqrt_pos.2 hxy
  have hsxy_le : Real.sqrt |x * y| ≤
      Real.pi * Real.sqrt (2 - Real.cos x - Real.cos y) := by
    have hsxySq := Real.sq_sqrt hxy.le
    have hsASq := Real.sq_sqrt hApos.le
    have hscaled : |x * y| ≤ Real.pi ^ 2 *
        (2 - Real.cos x - Real.cos y) := by
      simpa only [mul_comm] using (div_le_iff₀ hpSq).mp hA
    have hsquare : (Real.sqrt |x * y|) ^ 2 ≤
        (Real.pi * Real.sqrt (2 - Real.cos x - Real.cos y)) ^ 2 := by
      rw [hsxySq, mul_pow, hsASq]
      exact hscaled
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg Real.pi_pos.le
      (Real.sqrt_nonneg _))).mp hsquare
  have hinv : 1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
      Real.pi / Real.sqrt |x * y| := by
    rw [div_le_div_iff₀ hsA hsxy]
    simpa [mul_comm] using hsxy_le
  calc
    1 / Real.sqrt (2 - Real.cos x - Real.cos y) ≤
        Real.pi / Real.sqrt |x * y| := hinv
    _ = Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) := by
      rw [abs_mul, Real.sqrt_mul (abs_nonneg x)]
      field_simp [Real.sqrt_ne_zero'.mpr (abs_pos.mpr hx0),
        Real.sqrt_ne_zero'.mpr (abs_pos.mpr hy0)]

theorem ons_logGIntBetaDeriv_abs_le_criticalProduct {b x y : ℝ}
    (hb : b ∈ ons_criticalParameterNeighborhood)
    (hx : x ∈ Set.Icc (-Real.pi) Real.pi)
    (hy : y ∈ Set.Icc (-Real.pi) Real.pi)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    |ons_logGIntBetaDeriv b x y| ≤
      32 * (Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) + 1) := by
  have hApos : 0 < 2 - Real.cos x - Real.cos y := by
    have hxy : 0 < |x * y| := abs_pos.mpr (mul_ne_zero hx0 hy0)
    have hpSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    exact (div_pos hxy hpSq).trans_le (ons_criticalDenom_lower_abs_mul hx hy)
  calc
    |ons_logGIntBetaDeriv b x y| ≤
        32 * (1 / Real.sqrt (2 - Real.cos x - Real.cos y) + 1) :=
      ons_logGIntBetaDeriv_abs_le_criticalA hb hApos
    _ ≤ 32 * (Real.pi * (1 / Real.sqrt |x|) * (1 / Real.sqrt |y|) + 1) := by
      gcongr
      exact ons_inv_sqrt_criticalDenom_le_product hx hy hx0 hy0

theorem ons_criticalParameterNeighborhood_isOpen :
    IsOpen ons_criticalParameterNeighborhood := by
  have hlin : Continuous (fun b : ℝ => 2 * b) := continuous_const.mul continuous_id
  have hsinh : Continuous (fun b : ℝ => Real.sinh (2 * b)) :=
    Real.continuous_sinh.comp hlin
  have hcoshAbs : Continuous (fun b : ℝ => |Real.cosh (2 * b)|) :=
    (Real.continuous_cosh.comp hlin).abs
  change IsOpen ({b : ℝ | (1 / 2 : ℝ) < Real.sinh (2 * b)} ∩
    {b : ℝ | |Real.cosh (2 * b)| < 2})
  exact (isOpen_lt continuous_const hsinh).inter
    (isOpen_lt hcoshAbs continuous_const)

end StatMech.Onsager
