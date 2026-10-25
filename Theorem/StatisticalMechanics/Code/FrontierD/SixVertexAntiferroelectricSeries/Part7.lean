/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

theorem alternatingHarmonicLimit_tendsto :
    Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℝ) ^ n * ((1 : ℝ) / (n + 1 : ℝ))) atTop
      (𝓝 sixVertexAlternatingHarmonicLimit) :=
  Classical.choose_spec (antitone_one_div_nat_succ.tendsto_alternating_series_of_tendsto_zero
    (by simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))


theorem sixVertexAlternatingHarmonicLimit_eq_log_two :
    sixVertexAlternatingHarmonicLimit = Real.log 2 := by
  have hab := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    alternatingHarmonicLimit_tendsto
  have hm : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 :=
    tendsto_nhdsWithin_of_tendsto_nhds fun _ h => h
  have habLog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] 1) (𝓝 sixVertexAlternatingHarmonicLimit) := by
    apply hab.congr'
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hx0 : x ≠ 0 := hx.1.ne'
    have hxmin : |-x| < 1 := by
      rw [abs_neg, abs_of_pos hx.1]
      exact hx.2
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one hxmin
    calc
      (∑' n : ℕ, (-1 : ℝ) ^ n * (1 / (n + 1 : ℝ)) * x ^ n) =
          ∑' n : ℕ,
            (-1 / x) * ((-x) ^ (n + 1) / (n + 1 : ℝ)) := by
        apply tsum_congr
        intro n
        rw [pow_succ, neg_pow]
        field_simp [hx0]
        ring
      _ = (-1 / x) *
          ∑' n : ℕ, (-x) ^ (n + 1) / (n + 1 : ℝ) := by
        rw [tsum_mul_left]
      _ = Real.log (1 + x) / x := by
        rw [hs.tsum_eq]
        rw [show 1 - -x = 1 + x by ring]
        field_simp [hx0]
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
        (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have hc : ContinuousAt (fun x : ℝ => Real.log (1 + x) / x) 1 := by
      exact ((continuousAt_const.add continuousAt_id).log (by norm_num)).div
        continuousAt_id (by norm_num)
    convert hc.tendsto.mono_left hm using 1
    all_goals norm_num
  exact tendsto_nhds_unique habLog hlog


end StatMech.FrontierD
