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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourier.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem one_lt_sixVertexRegularizedRapidityDelta
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    1 < sixVertexRegularizedRapidityDelta lam epsilon := by
  have hd : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
  have hB : 0 < sixVertexRegularizedRapidityB lam epsilon := by
    unfold sixVertexRegularizedRapidityB
    positivity
  unfold sixVertexRegularizedRapidityDelta
  rw [one_lt_div hB]
  unfold sixVertexRegularizedRapidityB
  nlinarith

theorem sixVertexRegularizedRapidityRadius_mem_Ioo
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    sixVertexRegularizedRapidityRadius lam epsilon ∈ Set.Ioo 0 1 := by
  let delta := sixVertexRegularizedRapidityDelta lam epsilon
  have hdelta : 1 < delta :=
    one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon
  have hmu : 0 < Real.arcosh delta := Real.arcosh_pos hdelta
  constructor
  · unfold sixVertexRegularizedRapidityRadius
    positivity
  · unfold sixVertexRegularizedRapidityRadius
    rw [Real.exp_lt_one_iff]
    linarith

theorem sixVertexRegularizedRapidityDelta_eq_radius
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    sixVertexRegularizedRapidityDelta lam epsilon =
      (sixVertexRegularizedRapidityRadius lam epsilon +
        (sixVertexRegularizedRapidityRadius lam epsilon)⁻¹) / 2 := by
  let delta := sixVertexRegularizedRapidityDelta lam epsilon
  let mu := Real.arcosh delta
  let r := Real.exp (-mu)
  have hdelta : 1 ≤ delta :=
    (one_lt_sixVertexRegularizedRapidityDelta hlam hepsilon).le
  have hcosh : Real.cosh mu = delta := Real.cosh_arcosh hdelta
  change delta = (r + r⁻¹) / 2
  rw [← hcosh, Real.cosh_eq]
  dsimp [r]
  rw [Real.exp_neg, inv_inv]
  ring

theorem neg_pi_le_pi : -Real.pi ≤ Real.pi := by
  linarith [Real.pi_pos]


theorem intervalIntegral_mul_sixVertexFourierPhysicalDensity_eq_rapidity
    {c : Real} (hc : 2 < c) {f : Real → Real} (hf : Continuous f) :
    (∫ x in -Real.pi..Real.pi,
      f x * sixVertexFourierPhysicalDensity c hc x) =
      (1 / (2 * Real.pi)) *
        ∫ alpha in -Real.pi..Real.pi,
          f (sixVertexRapidityMomentum
              (sixVertexAntiferroelectricLambda c) alpha) *
            sixVertexFourierRootDensity
              (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  let g : Real → Real := fun x =>
    f x * sixVertexFourierPhysicalDensity c hc x
  have hg : Continuous g :=
    hf.mul (continuous_sixVertexFourierPhysicalDensity hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi)
    (f := sixVertexRapidityMomentum lam)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun alpha _ => hasDerivAt_sixVertexRapidityMomentum hlam alpha)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  rw [sixVertexRapidityMomentum_neg_pi hlam,
    sixVertexRapidityMomentum_pi hlam] at hsubst
  rw [← hsubst]
  have hpull :
      (∫ alpha in -Real.pi..Real.pi,
        (g ∘ sixVertexRapidityMomentum lam) alpha *
          sixVertexXiFourier lam alpha) =
      ∫ alpha in -Real.pi..Real.pi,
        (f (sixVertexRapidityMomentum lam alpha) *
          sixVertexFourierRootDensity lam alpha) / (2 * Real.pi) := by
    apply intervalIntegral.integral_congr
    intro alpha halpha
    rw [Set.uIcc_of_le neg_pi_le_pi] at halpha
    dsimp only [Function.comp_apply, g]
    rw [sixVertexFourierPhysicalDensity_rapidityMomentum hc halpha]
    have hXi : sixVertexXiFourier lam alpha ≠ 0 :=
      (sixVertexXiFourier_pos hlam alpha).ne'
    dsimp [lam] at hXi ⊢
    field_simp [hXi, Real.pi_ne_zero]
  rw [hpull]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  ring

theorem sixVertexBetheLogNumerator_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    sixVertexBetheLogNumerator c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      2 * (Real.cosh (sixVertexAntiferroelectricLambda c) + 1) *
        (Real.cosh (2 * sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) /
        (Real.cosh (sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hrel := sixVertex_cosh_antiferroelectricLambda hc
  have hhyper := Real.cosh_sq_sub_sinh_sq lam
  rw [sixVertexBetheLogNumerator,
    cos_sixVertexRapidityMomentum hlam]
  rw [Real.cosh_two_mul]
  rw [eq_div_iff hd]
  field_simp [hd]
  dsimp [lam] at hrel hhyper ⊢
  rw [hrel] at hhyper ⊢
  ring_nf at hhyper ⊢
  nlinarith

theorem sixVertexBetheLogDenominator_rapidityMomentum
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexBetheLogDenominator
          (sixVertexRapidityMomentum
            (sixVertexAntiferroelectricLambda c) alpha) + epsilon =
      sixVertexRegularizedRapidityB
          (sixVertexAntiferroelectricLambda c) epsilon *
        (sixVertexRegularizedRapidityDelta
            (sixVertexAntiferroelectricLambda c) epsilon -
          Real.cos alpha) /
        (Real.cosh (sixVertexAntiferroelectricLambda c) -
          Real.cos alpha) := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hd : Real.cosh lam - Real.cos alpha ≠ 0 := by
    have := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  rw [sixVertexBetheLogDenominator,
    cos_sixVertexRapidityMomentum hlam]
  unfold sixVertexRegularizedRapidityDelta
  have hB : sixVertexRegularizedRapidityB lam epsilon ≠ 0 := by
    unfold sixVertexRegularizedRapidityB
    positivity
  unfold sixVertexRegularizedRapidityB
  dsimp [lam] at hd hB ⊢
  field_simp [hd, hB]
  ring

end
end StatMech.FrontierD
