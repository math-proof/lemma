/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectiveBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.ConnectiveBounds.Part5


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma zd_one_le_sawCountR {d : ℕ} (hd : 1 ≤ d) (n : ℕ) : 1 ≤ zdSAWCountR d n := by
  unfold zdSAWCountR; exact_mod_cast zd_one_le_sawCount hd n

lemma zd_sawCountR_submult (d : ℕ) : Submultiplicative (zdSAWCountR d) := by
  intro m n
  unfold zdSAWCountR
  have := zd_sawCount_submult d m n
  exact_mod_cast this


theorem zd_connectiveConstant_exists {d : ℕ} (hd : 1 ≤ d) :
    ∃ μ : ℝ, 0 < μ ∧
      Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) :=
  connectiveConstant_tendsto (zd_one_le_sawCountR hd) (zd_sawCountR_submult d)


theorem zd_le_connectiveConstant {d : ℕ} {μ : ℝ}
    (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
    (d : ℝ) ≤ μ := by
  refine ge_of_tendsto hμ ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  
  have hdn : ((d : ℝ) ^ n) ≤ zdSAWCountR d n := by
    unfold zdSAWCountR; exact_mod_cast (zd_pow_le_sawCount (d := d) (n := n))
  have hbase : (0 : ℝ) ≤ (d : ℝ) ^ n := by positivity
  have hmono : ((d : ℝ) ^ n) ^ ((n : ℝ)⁻¹) ≤ (zdSAWCountR d n) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow hbase hdn (by positivity)
  have hpow : ((d : ℝ) ^ n) ^ ((n : ℝ)⁻¹) = (d : ℝ) := by
    rw [← Real.rpow_natCast (d : ℝ) n, ← Real.rpow_mul (by positivity)]
    rw [mul_inv_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  rw [hpow] at hmono
  exact hmono


lemma zd_upperSeq_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => ((2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1)) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 (2 * (d : ℝ) - 1)) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2d1 : (0 : ℝ) < 2 * (d : ℝ) - 1 := by linarith
  set A := Real.log (2 * (d : ℝ))
  set L := Real.log (2 * (d : ℝ) - 1)
  have hlog : Tendsto (fun n : ℕ => (A + ((n : ℝ) - 1) * L) / n) atTop (𝓝 L) := by
    have heq : (fun n : ℕ => (A + ((n : ℝ) - 1) * L) / n)
        =ᶠ[atTop] (fun n : ℕ => (A - L) / n + L) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp; ring
    rw [tendsto_congr' heq]
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (A - L)).add (tendsto_const_nhds (x := L))
  have hexp : Tendsto (fun n : ℕ => Real.exp ((A + ((n : ℝ) - 1) * L) / n)) atTop
      (𝓝 (Real.exp L)) := (Real.continuous_exp.tendsto L).comp hlog
  rw [Real.exp_log h2d1] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn; exact_mod_cast this.ne'
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_eq_exp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  congr 1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast]


theorem zd_connectiveConstant_le {d : ℕ} (hd : 1 ≤ d) {μ : ℝ}
    (hμ : Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ)) :
    μ ≤ 2 * (d : ℝ) - 1 := by
  refine le_of_tendsto_of_tendsto hμ (zd_upperSeq_tendsto hd) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  
  have hub : zdSAWCountR d n ≤ (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := by
    unfold zdSAWCountR
    have := zd_sawCount_le (d := d) (n := n) hn
    have hcast : ((2 * d * (2 * d - 1) ^ (n - 1) : ℕ) : ℝ)
        = (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := by
      have hdge : 1 ≤ 2 * d := by omega
      push_cast [Nat.cast_sub hdge]
      ring
    calc (zdSAWCount d n : ℝ) ≤ ((2 * d * (2 * d - 1) ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (2 * (d : ℝ)) * (2 * (d : ℝ) - 1) ^ (n - 1) := hcast
  exact Real.rpow_le_rpow (by unfold zdSAWCountR; positivity) hub (by positivity)


theorem zd_connectiveConstant_bounds {d : ℕ} (hd : 1 ≤ d) :
    ∃ μ : ℝ, 0 < μ ∧
      Tendsto (fun n => (zdSAWCountR d n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 μ) ∧
      (d : ℝ) ≤ μ ∧ μ ≤ 2 * (d : ℝ) - 1 := by
  obtain ⟨μ, hμpos, hμtend⟩ := zd_connectiveConstant_exists hd
  exact ⟨μ, hμpos, hμtend, zd_le_connectiveConstant hμtend, zd_connectiveConstant_le hd hμtend⟩

end StatMech.Universality
