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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part8
open Finset Filter Topology


namespace StatMech.FrontierD

theorem sixVertexGapSeries_eq_lambert (lam : ℝ) :
    sixVertexGapSeries lam =
      -Real.log 2 +
        ∑' n : ℕ, sixVertexGapLambertTerm lam n := by
  unfold sixVertexGapSeries
  congr 1
  apply tsum_congr
  exact sixVertexGapCorrectionTerm_eq_lambert lam


theorem sixVertexGapSeries_partialSum_tendsto {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, sixVertexGapSeriesTerm lam n) atTop
      (𝓝 (sixVertexGapSeries lam)) := by
  have hharmonic := alternatingHarmonicLimit_tendsto.neg
  rw [sixVertexAlternatingHarmonicLimit_eq_log_two] at hharmonic
  have hcorrection := (summable_sixVertexGapCorrectionTerm hlam).hasSum.tendsto_sum_nat
  have hadd := hharmonic.add hcorrection
  rw [← show -Real.log 2 +
      ∑' n : ℕ, sixVertexGapCorrectionTerm lam n = sixVertexGapSeries lam by rfl]
  apply hadd.congr'
  filter_upwards [] with N
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sixVertexGapSeriesTerm, sixVertexGapCorrectionTerm, pow_succ]
  ring


end StatMech.FrontierD
