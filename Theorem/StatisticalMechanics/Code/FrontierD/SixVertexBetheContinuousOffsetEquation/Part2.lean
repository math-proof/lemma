/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2
import Mathlib.Analysis.Calculus.SmoothSeries
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem norm_sixVertexOffsetConvolutionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetConvolutionTerm lam n alpha‖ <=
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  unfold sixVertexOffsetConvolutionTerm
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_div, abs_mul,
    abs_of_nonneg (by positivity : (0 : Real) <= 2),
    abs_of_pos (Real.exp_pos _), abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : Real) < (n + 1 : Real))]
  have htanh : |Real.tanh ((n + 1 : Real) * lam)| <= 1 :=
    (Real.abs_tanh_lt_one _).le
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hfrac : |Real.tanh ((n + 1 : Real) * lam)| /
      (n + 1 : Real) <= 1 := by
    have hn : 1 <= (n + 1 : Real) := by norm_num
    exact (div_le_one (by positivity)).2 (htanh.trans hn)
  have hprod :
      (|Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
          |Real.sin ((n + 1 : Real) * alpha)| <= 1 := by
    nlinarith [mul_le_mul hfrac hsin (abs_nonneg _) (by positivity : (0 : Real) <= 1)]
  have hexp :
      Real.exp (-2 * ((n + 1 : Real) * lam)) =
        Real.exp (-2 * lam) ^ (n + 1) := by
    rw [<- Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    2 * Real.exp (-2 * lam) ^ (n + 1) *
          (1 * |Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
          |Real.sin ((n + 1 : Real) * alpha)| =
        (2 * Real.exp (-2 * lam) ^ (n + 1)) *
          ((|Real.tanh ((n + 1 : Real) * lam)| / (n + 1 : Real)) *
            |Real.sin ((n + 1 : Real) * alpha)|) := by ring
    _ <= (2 * Real.exp (-2 * lam) ^ (n + 1)) * 1 :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

theorem summable_sixVertexOffsetConvolutionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetConvolutionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetConvolutionTerm_le lam n alpha)

theorem intervalIntegral_shiftedCos_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) {m : Nat} (hm : 0 < m)
    (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      Real.cos ((m : Real) * (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) =
      Real.sin ((m : Real) * alpha) *
        ((-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (m : Real)) := by
  let tau := sixVertexOffsetRapidityProfile lam
  have htau : Continuous tau :=
    continuous_sixVertexOffsetRapidityProfile hlam
  have hcosZero :
      (∫ beta in -Real.pi..Real.pi,
        Real.cos ((m : Real) * beta) * tau beta) = 0 := by
    apply intervalIntegral_neg_pi_pi_eq_zero_of_odd
    intro beta
    dsimp [tau]
    rw [show (m : Real) * -beta = -((m : Real) * beta) by ring,
      Real.cos_neg, odd_sixVertexOffsetRapidityProfile]
    ring
  have hsinCoeff :
      (∫ beta in -Real.pi..Real.pi,
        tau beta * Real.sin ((m : Real) * beta)) =
      (-1 : Real) ^ m * Real.tanh ((m : Real) * lam) / (m : Real) := by
    have h := sixVertexOffsetRapidityProfile_sineCoefficient hlam hm
    calc
      _ = Real.pi * ((1 / Real.pi) *
          ∫ beta in -Real.pi..Real.pi,
            tau beta * Real.sin ((m : Real) * beta)) := by
        field_simp [Real.pi_ne_zero]
      _ = Real.pi *
          ((-1 : Real) ^ m * Real.tanh ((m : Real) * lam) /
            (Real.pi * (m : Real))) := by rw [h]
      _ = _ := by
        field_simp [Real.pi_ne_zero,
          show (m : Real) ≠ 0 by exact_mod_cast hm.ne']
  have hcosInt : IntervalIntegrable
      (fun beta => Real.cos ((m : Real) * beta) * tau beta)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((by fun_prop : Continuous (fun beta : Real =>
      Real.cos ((m : Real) * beta))).mul htau).intervalIntegrable _ _
  have hsinInt : IntervalIntegrable
      (fun beta => Real.sin ((m : Real) * beta) * tau beta)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    ((by fun_prop : Continuous (fun beta : Real =>
      Real.sin ((m : Real) * beta))).mul htau).intervalIntegrable _ _
  have hpoint (beta : Real) :
      Real.cos ((m : Real) * (alpha - beta)) * tau beta =
        Real.cos ((m : Real) * alpha) *
            (Real.cos ((m : Real) * beta) * tau beta) +
          Real.sin ((m : Real) * alpha) *
            (Real.sin ((m : Real) * beta) * tau beta) := by
    rw [mul_sub, Real.cos_sub]
    ring
  rw [intervalIntegral.integral_congr (fun beta _ => hpoint beta),
    intervalIntegral.integral_add
    (hcosInt.const_mul _) (hsinInt.const_mul _),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcosZero]
  have hsinComm :
      (∫ beta in -Real.pi..Real.pi,
        Real.sin ((m : Real) * beta) * tau beta) =
      ∫ beta in -Real.pi..Real.pi,
        tau beta * Real.sin ((m : Real) * beta) := by
    apply intervalIntegral.integral_congr
    intro beta _
    ring
  rw [hsinComm, hsinCoeff]
  ring

theorem intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
        sixVertexOffsetRapidityProfile lam beta) =
      sixVertexOffsetConvolutionTerm lam n alpha := by
  unfold sixVertexXiFourierTerm sixVertexOffsetConvolutionTerm
  rw [show (fun beta : Real =>
      (2 * Real.exp (-((n + 1 : Real) * (2 * lam))) *
          Real.cos ((n + 1 : Real) * (alpha - beta))) *
          sixVertexOffsetRapidityProfile lam beta) =
      fun beta =>
        (2 * Real.exp (-((n + 1 : Real) * (2 * lam)))) *
          (Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexOffsetRapidityProfile lam beta) by
    funext beta
    ring,
    intervalIntegral.integral_const_mul,
    show (∫ beta in -Real.pi..Real.pi,
        Real.cos ((n + 1 : Real) * (alpha - beta)) *
          sixVertexOffsetRapidityProfile lam beta) =
        Real.sin ((n + 1 : Real) * alpha) *
          ((-1 : Real) ^ (n + 1) *
            Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real)) by
      simpa only [Nat.cast_add, Nat.cast_one] using
        intervalIntegral_shiftedCos_mul_offsetRapidityProfile hlam
          (m := n + 1) (by omega) alpha]
  ring

end
end StatMech.FrontierD
