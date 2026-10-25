/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PhaseRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CriticalIntegrability.Part3
import Def.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part6


namespace StatMech.Onsager

theorem ons_one_div_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hx]

theorem ons_criticalOneDimMajorant_intervalIntegrable :
    IntervalIntegrable ons_criticalOneDimMajorant MeasureTheory.volume
      (-Real.pi) Real.pi := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 Real.pi :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpos : IntervalIntegrable ons_criticalOneDimMajorant
      MeasureTheory.volume 0 Real.pi := by
    apply hpow.congr
    intro x hx
    rw [Set.uIoc_of_le Real.pi_pos.le] at hx
    simp only [ons_criticalOneDimMajorant, abs_of_nonneg hx.1.le]
    exact (ons_one_div_sqrt_eq_rpow_neg_half hx.1.le).symm
  have hnegRaw := hpos.comp_mul_left (c := (-1 : ℝ))
  have hnegOriented : IntervalIntegrable
      (fun x => ons_criticalOneDimMajorant (-x))
      MeasureTheory.volume 0 (-Real.pi) := by
    simpa only [zero_div, div_neg, div_one, neg_mul, one_mul, neg_zero] using hnegRaw
  have hnegOriented' : IntervalIntegrable ons_criticalOneDimMajorant
      MeasureTheory.volume 0 (-Real.pi) := by
    apply hnegOriented.congr
    intro x _hx
    simp [ons_criticalOneDimMajorant]
  exact hnegOriented'.symm.trans hpos

end StatMech.Onsager
