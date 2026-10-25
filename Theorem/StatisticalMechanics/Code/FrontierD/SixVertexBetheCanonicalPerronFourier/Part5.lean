/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexRegularizedRapidityConstant
          (sixVertexAntiferroelectricLambda c) epsilon +
        sixVertexLogCosineSeries
          (sixVertexRegularizedRapidityRadius
            (sixVertexAntiferroelectricLambda c) epsilon) alpha -
        sixVertexLogCosineSeries
          (sixVertexFreeEnergyRapidityRadius
            (sixVertexAntiferroelectricLambda c)) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hq : q ∈ Set.Ioo 0 1 :=
    sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr : r ∈ Set.Ioo 0 1 :=
    sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hqAbs : |q| < 1 := by
    rw [abs_of_pos hq.1]
    exact hq.2
  have hrAbs : |r| < 1 := by
    rw [abs_of_pos hr.1]
    exact hr.2
  have hd : 0 < Real.cosh lam - Real.cos alpha := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hD : 0 < Real.cosh (2 * lam) - Real.cos alpha := by
    have h2lam : 0 < 2 * lam := by positivity
    have := Real.one_lt_cosh.mpr h2lam.ne'
    linarith [Real.cos_le_one alpha]
  have hdelta : 0 < sixVertexRegularizedRapidityDelta lam epsilon -
      Real.cos alpha := by
    have := one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon
    linarith [Real.cos_le_one alpha]
  have hA : 0 < 2 * (Real.cosh lam + 1) := by positivity
  have hB : 0 < sixVertexRegularizedRapidityB lam epsilon := by
    unfold sixVertexRegularizedRapidityB
    positivity
  have hnum := sixVertexBetheLogNumerator_rapidityMomentum hc alpha
  have hden := sixVertexBetheLogDenominator_rapidityMomentum
    hc hepsilon alpha
  have hqlog :
      Real.log (Real.cosh (2 * lam) - Real.cos alpha) =
        2 * Real.log ‖(1 : Complex) -
            (q : Complex) * Complex.exp (Complex.I * alpha)‖ -
          Real.log (2 * q) := by
    rw [cosh_two_eq_sixVertexFreeEnergyRapidityRadius]
    exact log_radius_add_inv_div_two_sub_cos hq alpha
  have hrlog :
      Real.log (sixVertexRegularizedRapidityDelta lam epsilon -
          Real.cos alpha) =
        2 * Real.log ‖(1 : Complex) -
            (r : Complex) * Complex.exp (Complex.I * alpha)‖ -
          Real.log (2 * r) := by
    rw [sixVertexRegularizedRapidityDelta_eq_radius hlam hepsilon]
    exact log_radius_add_inv_div_two_sub_cos hr alpha
  have hnumlog :
      Real.log (sixVertexBetheLogNumerator c
          (sixVertexRapidityMomentum lam alpha)) =
        Real.log (2 * (Real.cosh lam + 1)) +
          Real.log (Real.cosh (2 * lam) - Real.cos alpha) -
          Real.log (Real.cosh lam - Real.cos alpha) := by
    rw [hnum]
    rw [Real.log_div (mul_ne_zero hA.ne' hD.ne') hd.ne',
      Real.log_mul hA.ne' hD.ne']
  have hdenlog :
      Real.log (sixVertexBetheLogDenominator
          (sixVertexRapidityMomentum lam alpha) + epsilon) =
        Real.log (sixVertexRegularizedRapidityB lam epsilon) +
          Real.log (sixVertexRegularizedRapidityDelta lam epsilon -
            Real.cos alpha) -
          Real.log (Real.cosh lam - Real.cos alpha) := by
    rw [hden]
    rw [Real.log_div (mul_ne_zero hB.ne' hdelta.ne') hd.ne',
      Real.log_mul hB.ne' hdelta.ne']
  rw [sixVertexRegularizedBetheLogKernel, hnumlog, hdenlog,
    hqlog, hrlog,
    sixVertexLogCosineSeries_eq_neg_log_norm
      (by simpa only [r] using hrAbs),
    sixVertexLogCosineSeries_eq_neg_log_norm
      (by simpa only [q] using hqAbs)]
  dsimp [sixVertexRegularizedRapidityConstant, lam, q, r]
  ring

end
end StatMech.FrontierD
