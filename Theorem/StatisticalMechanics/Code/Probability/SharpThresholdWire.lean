/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/SharpThresholdWire.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.HCTensorLib
import Theorem.StatisticalMechanics.Code.Probability.PBiasedHCLib.Part3
open scoped BigOperators
open Finset
open Real Set
open StatMech StatMech.OSSS

set_option linter.style.longLine false


namespace StatMech.Probability

theorem stw_master_q_value {u : ℝ} (ρ : ℝ) (hρsq : ρ ^ 2 = 1 - u) :
    (1 + ρ ^ 2 : ℝ) = 2 - u := by
  rw [hρsq]; ring


theorem stw_master_uses_exponent_le_two {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    1 < 2 - u ∧ 2 - u ≤ 2 := ⟨by linarith, by linarith⟩


theorem stw_ranges_meet_only_at_two {q : ℝ} (hfwd : 2 ≤ q ∧ q ≤ 4) (hmaster : 1 < q ∧ q ≤ 2) :
    q = 2 := le_antisymm hmaster.2 hfwd.1


theorem stw_variance_coeff_gap {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    4 * p ^ 2 * (1 - p) ^ 2 ≤ p * (1 - p) := by
  nlinarith [mul_nonneg hp0 (by linarith : (0:ℝ) ≤ 1 - p), sq_nonneg (1 - 2 * p),
    mul_nonneg (mul_nonneg hp0 (by linarith : (0:ℝ) ≤ 1 - p)) (sq_nonneg (1 - 2 * p))]


theorem stw_coeff_gap_eq_iff_half {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    4 * p ^ 2 * (1 - p) ^ 2 = p * (1 - p) ↔ p = 1 / 2 := by
  constructor
  · intro h
    have hpos : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
    
    have hfac : p * (1 - p) * (1 - 4 * p * (1 - p)) = 0 := by nlinarith [h]
    have h4 : 1 - 4 * p * (1 - p) = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    have hsq : (1 - 2 * p) ^ 2 = 0 := by nlinarith [h4]
    have : 1 - 2 * p = 0 := by nlinarith [sq_nonneg (1 - 2 * p), hsq]
    linarith
  · intro h; rw [h]; norm_num


theorem stw_pbiasedHCLib_implies_proved_lhs {p ρ u v : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((1 - p) * u + p * v) ^ 2 + (ρ ^ 2 + 1 - 1) * 4 * p ^ 2 * (1 - p) ^ 2 * (u - v) ^ 2
      ≤ ((1 - p) * u + p * v) ^ 2 + ρ ^ 2 * (p * (1 - p)) * (u - v) ^ 2 := by
  have hgap := stw_variance_coeff_gap hp0 hp1
  nlinarith [sq_nonneg (u - v), sq_nonneg ρ,
    mul_nonneg (sq_nonneg ρ) (sq_nonneg (u - v)),
    mul_nonneg (mul_nonneg (sq_nonneg ρ) (by linarith [hgap] : (0:ℝ) ≤ p * (1 - p) - 4 * p ^ 2 * (1 - p) ^ 2)) (sq_nonneg (u - v))]


theorem stw_pbiasedHCLib_half : PBiasedHCLib (1 / 2) := htl_lib_half


theorem stw_kkl_logGain_half {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (φ : ConfigSpace ι → Bool) :
    2 * (OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0)
          * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2 : ℝ))
              (fun ω => if φ ω then (1 : ℝ) else 0)))
        * Real.log (1 / maxInfl (OSSS.bernoulliWeight (1 / 2 : ℝ))
            (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (OSSS.bernoulliWeight (1 / 2 : ℝ)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  htl_kkl_logGain_half φ


end StatMech.Probability
