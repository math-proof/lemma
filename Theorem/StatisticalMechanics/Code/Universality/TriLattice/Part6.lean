/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/TriLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.SAW
import Def.StatisticalMechanics.Code.Universality.TriLattice.Part6


namespace StatMech.Universality

open Filter Topology Finset

open scoped Topology

open Classical


lemma tri_one_le_sawCountR (n : ℕ) : 1 ≤ triSAWCountR n := by
  unfold triSAWCountR; exact_mod_cast tri_one_le_sawCount n

lemma tri_sawCountR_submult : Submultiplicative triSAWCountR := by
  intro m n
  unfold triSAWCountR
  have := tri_sawCount_submult m n
  exact_mod_cast this


theorem tri_connectiveConstant_exists :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) :=
  connectiveConstant_tendsto tri_one_le_sawCountR tri_sawCountR_submult


theorem tri_le_connectiveConstant {κ : ℝ}
    (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
    (3 : ℝ) ≤ κ := by
  refine ge_of_tendsto hκ ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdn : ((3 : ℝ) ^ n) ≤ triSAWCountR n := by
    unfold triSAWCountR; exact_mod_cast (tri_pow_le_sawCount (n := n))
  have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ n := by positivity
  have hmono : ((3 : ℝ) ^ n) ^ ((n : ℝ)⁻¹) ≤ (triSAWCountR n) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_le_rpow hbase hdn (by positivity)
  have hpow : ((3 : ℝ) ^ n) ^ ((n : ℝ)⁻¹) = (3 : ℝ) := by
    rw [← Real.rpow_natCast (3 : ℝ) n, ← Real.rpow_mul (by positivity)]
    rw [mul_inv_cancel₀ (ne_of_gt hnR), Real.rpow_one]
  rw [hpow] at hmono
  exact hmono


lemma tri_upperSeq_tendsto :
    Tendsto (fun n : ℕ => ((6 : ℝ) * (5 : ℝ) ^ (n - 1)) ^ ((n : ℝ)⁻¹))
      atTop (𝓝 5) := by
  set A := Real.log 6
  set L := Real.log 5
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
  have h5 : Real.exp L = 5 := by simp [L, Real.exp_log]
  rw [h5] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by
    have : 0 < n := hn; exact_mod_cast this.ne'
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_eq_exp,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  congr 1
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; push_cast; ring
  rw [hcast]


theorem tri_connectiveConstant_le {κ : ℝ}
    (hκ : Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ)) :
    κ ≤ 5 := by
  refine le_of_tendsto_of_tendsto hκ tri_upperSeq_tendsto ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hub : triSAWCountR n ≤ (6 : ℝ) * (5 : ℝ) ^ (n - 1) := by
    unfold triSAWCountR
    have := tri_sawCount_le (n := n) hn
    have hcast : ((6 * 5 ^ (n - 1) : ℕ) : ℝ) = (6 : ℝ) * (5 : ℝ) ^ (n - 1) := by
      push_cast; ring
    calc (triSAWCount n : ℝ) ≤ ((6 * 5 ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (6 : ℝ) * (5 : ℝ) ^ (n - 1) := hcast
  exact Real.rpow_le_rpow (by unfold triSAWCountR; positivity) hub (by positivity)


theorem tri_connectiveConstant_bounds :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n => (triSAWCountR n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) ∧
      (3 : ℝ) ≤ κ ∧ κ ≤ 5 := by
  obtain ⟨κ, hκpos, hκtend⟩ := tri_connectiveConstant_exists
  exact ⟨κ, hκpos, hκtend, tri_le_connectiveConstant hκtend, tri_connectiveConstant_le hκtend⟩

end StatMech.Universality
