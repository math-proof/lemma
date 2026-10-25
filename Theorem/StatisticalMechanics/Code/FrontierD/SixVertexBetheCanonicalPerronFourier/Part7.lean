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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronRegularizedIntegral_eq_fourierValue
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    (∫ y in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogKernel c epsilon y *
        sixVertexFourierPhysicalDensity c hc y) =
      sixVertexRegularizedRapidityFourierValue
        (sixVertexAntiferroelectricLambda c) epsilon := by
  let lam := sixVertexAntiferroelectricLambda c
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  let C := sixVertexRegularizedRapidityConstant lam epsilon
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hq : q ∈ Set.Ioo 0 1 :=
    sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr : r ∈ Set.Ioo 0 1 :=
    sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hqAbs : |q| < 1 := by rw [abs_of_pos hq.1]; exact hq.2
  have hrAbs : |r| < 1 := by rw [abs_of_pos hr.1]; exact hr.2
  have hSr : Continuous (sixVertexLogCosineSeries r) := by
    apply continuous_tsum
    · intro n
      fun_prop
    · exact (summable_geometric_of_lt_one (abs_nonneg r) hrAbs).comp_injective
        Nat.succ_injective
    · intro n alpha
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
      have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
        abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hm : 1 <= |(n + 1 : Real)| := by
        have hpos : (0 : Real) < (n : Real) + 1 := by positivity
        rw [abs_of_pos hpos]
        norm_num
      calc
        |r| ^ (n + 1) * |Real.cos ((n + 1 : Real) * alpha)| /
            |(n + 1 : Real)| <= |r| ^ (n + 1) * 1 / 1 := by gcongr
        _ = |r| ^ (n + 1) := by ring
  have hSq : Continuous (sixVertexLogCosineSeries q) := by
    apply continuous_tsum
    · intro n
      fun_prop
    · exact (summable_geometric_of_lt_one (abs_nonneg q) hqAbs).comp_injective
        Nat.succ_injective
    · intro n alpha
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
      have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
        abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      have hm : 1 <= |(n + 1 : Real)| := by
        have hpos : (0 : Real) < (n : Real) + 1 := by positivity
        rw [abs_of_pos hpos]
        norm_num
      calc
        |q| ^ (n + 1) * |Real.cos ((n + 1 : Real) * alpha)| /
            |(n + 1 : Real)| <= |q| ^ (n + 1) * 1 / 1 := by gcongr
        _ = |q| ^ (n + 1) := by ring
  rw [intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity
    hc (continuous_sixVertexRegularizedBetheLogKernel hc hepsilon)]
  have hpoint : ∀ alpha : Real,
      sixVertexRegularizedBetheLogKernel c epsilon
          (sixVertexRapidityMomentum lam alpha) *
        sixVertexFourierRootDensity lam alpha =
      ((C + sixVertexLogCosineSeries r alpha) *
          sixVertexFourierRootDensity lam alpha) -
        sixVertexLogCosineSeries q alpha *
          sixVertexFourierRootDensity lam alpha := by
    intro alpha
    rw [sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
      hc hepsilon]
    dsimp only [lam, q, r, C]
    ring
  rw [intervalIntegral.integral_congr (fun alpha _ => hpoint alpha)]
  have hR := continuous_sixVertexFourierRootDensity hlam
  have hCR : IntervalIntegrable
      (fun alpha => C * sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((continuous_const : Continuous (fun _ : Real => C)).mul hR)
      |>.intervalIntegrable _ _
  have hSrR : IntervalIntegrable
      (fun alpha => sixVertexLogCosineSeries r alpha *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hSr.mul hR).intervalIntegrable _ _
  have hSqR : IntervalIntegrable
      (fun alpha => sixVertexLogCosineSeries q alpha *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hSq.mul hR).intervalIntegrable _ _
  have hCSrR : IntervalIntegrable
      (fun alpha => (C + sixVertexLogCosineSeries r alpha) *
        sixVertexFourierRootDensity lam alpha)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (((continuous_const : Continuous (fun _ : Real => C)).add hSr).mul hR)
      |>.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hCSrR hSqR]
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add hCR hSrR,
    intervalIntegral.integral_const_mul,
    intervalIntegral_sixVertexFourierRootDensity hlam,
    intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity hlam hrAbs,
    intervalIntegral_sixVertexLogCosineSeries_mul_rootDensity hlam hqAbs]
  have hsumr := summable_sixVertexAbelRootDensitySeriesTerm
    (lam := lam) hrAbs
  have hsumq := summable_sixVertexAbelRootDensitySeriesTerm
    (lam := lam) hqAbs
  have hpir : (∑' n : Nat,
      Real.pi * r ^ (n + 1) /
          ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))) =
      Real.pi * ∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam r n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold sixVertexAbelRootDensitySeriesTerm
    ring
  have hpiq : (∑' n : Nat,
      Real.pi * q ^ (n + 1) /
          ((n + 1 : Real) * Real.cosh ((n + 1 : Real) * lam))) =
      Real.pi * ∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam q n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    unfold sixVertexAbelRootDensitySeriesTerm
    ring
  rw [hpir, hpiq]
  rw [show C * Real.pi + Real.pi * (∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam r n) -
      Real.pi * (∑' n : Nat,
        sixVertexAbelRootDensitySeriesTerm lam q n) =
      C * Real.pi + Real.pi *
        ((∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam r n) -
          ∑' n : Nat, sixVertexAbelRootDensitySeriesTerm lam q n) by ring,
    ← hsumr.tsum_sub hsumq]
  unfold sixVertexRegularizedRapidityFourierValue
  dsimp only [lam, q, r, C]
  field_simp [Real.pi_ne_zero]
  <;> ring

end
end StatMech.FrontierD
