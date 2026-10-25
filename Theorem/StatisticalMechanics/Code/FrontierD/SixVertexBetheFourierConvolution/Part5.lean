/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part5


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_XiFourier_mul_rootDensity
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourier (2 * lam) (alpha - beta) *
        sixVertexFourierRootDensity lam beta) =
      Real.pi + ∑' n : Nat, sixVertexXiRootConvolutionTerm lam n alpha := by
  have h2lam : 0 < 2 * lam := mul_pos (by norm_num) hlam
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hmajorMul : Summable (fun n : Nat =>
      sixVertexFourierRootDensityMajorant (2 * lam) n *
        sixVertexFourierRootDensityNormBound lam) := by
    simpa [mul_comm] using Summable.mul_left
      (sixVertexFourierRootDensityNormBound lam)
      (summable_sixVertexFourierRootDensityMajorant h2lam)
  have hnorm : Summable (fun n : Nat =>
      ‖(XiFourierTermMulRootDensityContinuous hlam n alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajorMul
    rw [ContinuousMap.norm_le _
      (mul_nonneg
        (by
          unfold sixVertexFourierRootDensityMajorant
          positivity)
        (sixVertexFourierRootDensityNormBound_nonneg lam))]
    intro beta
    change |sixVertexXiFourierTerm (2 * lam) n (alpha - (beta : Real)) *
      sixVertexFourierRootDensity lam beta| <= _
    rw [abs_mul]
    apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - (beta : Real))
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexFourierRootDensity_le hlam (beta : Real)
    · exact abs_nonneg _
    · unfold sixVertexFourierRootDensityMajorant
      positivity
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta) := by
    simpa only [XiFourierTermMulRootDensityContinuous] using hswap
  have hrootInt : IntervalIntegrable
      (sixVertexFourierRootDensity lam) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (continuous_sixVertexFourierRootDensity hlam).intervalIntegrable _ _
  have hseriesContinuous : Continuous
      (fun beta => ∑' n : Nat,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) := by
    apply continuous_tsum
    · intro n
      unfold sixVertexXiFourierTerm
      fun_prop
    · exact summable_sixVertexFourierRootDensityMajorant h2lam
    · intro n beta
      exact norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - beta)
  have hseriesInt : IntervalIntegrable
      (fun beta => (∑' n : Nat,
          sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (hseriesContinuous.mul (continuous_sixVertexFourierRootDensity hlam))
      |>.intervalIntegrable _ _
  simp_rw [sixVertexXiFourier]
  rw [show (fun beta =>
      (1 + ∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexFourierRootDensity lam beta) =
      (fun beta => sixVertexFourierRootDensity lam beta +
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexFourierRootDensity lam beta) by
      funext beta
      ring]
  rw [intervalIntegral.integral_add hrootInt hseriesInt,
    intervalIntegral_sixVertexFourierRootDensity hlam]
  have hseriesSwap :
      (∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexFourierRootDensity lam beta) =
      ∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexFourierRootDensity lam beta := by
    calc
      _ = ∫ beta in -Real.pi..Real.pi,
          (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
            sixVertexFourierRootDensity lam beta) := by
        apply intervalIntegral.integral_congr
        intro beta _
        exact tsum_mul_right.symm
      _ = _ := hswap'.symm
  rw [hseriesSwap]
  congr 1
  apply tsum_congr
  intro n
  exact intervalIntegral_XiFourierTerm_mul_rootDensity hlam n alpha

theorem norm_sixVertexXiRootConvolutionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexXiRootConvolutionTerm lam n alpha‖ <=
      Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n := by
  have hpi : 0 <= Real.pi := Real.pi_pos.le
  have hmajor : 0 <= sixVertexFourierRootDensityMajorant (2 * lam) n := by
    unfold sixVertexFourierRootDensityMajorant
    positivity
  have hcosh : 1 <= Real.cosh ((n + 1 : Real) * lam) := Real.one_le_cosh _
  have hcoshPos : 0 < Real.cosh ((n + 1 : Real) * lam) := Real.cosh_pos _
  have hxi := norm_sixVertexXiFourierTerm_le (2 * lam) n alpha
  have hrepr : sixVertexXiRootConvolutionTerm lam n alpha =
      Real.pi * sixVertexXiFourierTerm (2 * lam) n alpha /
        Real.cosh ((n + 1 : Real) * lam) := by
    unfold sixVertexXiRootConvolutionTerm sixVertexXiFourierTerm
    ring
  rw [hrepr, norm_div, norm_mul, Real.norm_of_nonneg hpi,
    Real.norm_of_nonneg hcoshPos.le]
  calc
    Real.pi * ‖sixVertexXiFourierTerm (2 * lam) n alpha‖ /
        Real.cosh ((n + 1 : Real) * lam)
      <= Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n /
          Real.cosh ((n + 1 : Real) * lam) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hxi hpi) hcoshPos.le
    _ <= Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n := by
      rw [div_le_iff₀ hcoshPos]
      nlinarith [mul_le_mul_of_nonneg_left hcosh hmajor]

theorem summable_sixVertexXiRootConvolutionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n : Nat => sixVertexXiRootConvolutionTerm lam n alpha) := by
  have h2lam : 0 < 2 * lam := mul_pos (by norm_num) hlam
  have hmajor : Summable (fun n : Nat =>
      Real.pi * sixVertexFourierRootDensityMajorant (2 * lam) n) :=
    Summable.mul_left Real.pi
      (summable_sixVertexFourierRootDensityMajorant h2lam)
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexXiRootConvolutionTerm_le lam n alpha)


theorem sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexXiFourierTerm lam n alpha -
        (1 / (2 * Real.pi)) * sixVertexXiRootConvolutionTerm lam n alpha =
      sixVertexFourierRootDensityTerm lam n alpha := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero _
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have hneg : Real.exp (-x) = (Real.exp x)⁻¹ := by
    rw [<- Real.exp_neg]
  have hnegTwo : Real.exp (-2 * x) =
      Real.exp (-x) * Real.exp (-x) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  have hexpProd : Real.exp x * Real.exp (-x) = 1 := by
    rw [<- Real.exp_add]
    simp
  unfold sixVertexXiFourierTerm sixVertexXiRootConvolutionTerm
    sixVertexFourierRootDensityTerm
  change 2 * Real.exp (-x) * Real.cos (m * alpha) -
      (1 / (2 * Real.pi)) *
        (2 * Real.exp (-2 * x) * Real.pi * Real.cos (m * alpha) /
          Real.cosh x) =
    Real.cos (m * alpha) / Real.cosh x
  rw [hnegTwo, hneg, Real.cosh_eq]
  field_simp [hexp, hpi]
  calc
    Real.cos (m * alpha) *
        (Real.exp x * (Real.exp x + Real.exp (-x)) - 1) =
      Real.exp x ^ 2 * Real.cos (m * alpha) +
        Real.cos (m * alpha) *
          (Real.exp x * Real.exp (-x) - 1) := by ring
    _ = Real.exp x ^ 2 * Real.cos (m * alpha) := by
      rw [hexpProd]
      ring


theorem sixVertexFourierRootDensity_integralEquation
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexFourierRootDensity lam alpha =
      sixVertexXiFourier lam alpha -
        (1 / (2 * Real.pi)) *
          ∫ beta in -Real.pi..Real.pi,
            sixVertexXiFourier (2 * lam) (alpha - beta) *
              sixVertexFourierRootDensity lam beta := by
  let q : Real := 1 / (2 * Real.pi)
  have hXi : Summable (fun n : Nat => sixVertexXiFourierTerm lam n alpha) :=
    summable_sixVertexXiFourierTerm hlam alpha
  have hConv : Summable (fun n : Nat =>
      sixVertexXiRootConvolutionTerm lam n alpha) :=
    summable_sixVertexXiRootConvolutionTerm hlam alpha
  have hRoot : Summable (fun n : Nat =>
      sixVertexFourierRootDensityTerm lam n alpha) :=
    summable_sixVertexFourierRootDensityTerm hlam alpha
  have hqConv : Summable (fun n : Nat =>
      q * sixVertexXiRootConvolutionTerm lam n alpha) :=
    Summable.mul_left q hConv
  have hseries :
      (∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha) =
        (∑' n : Nat, sixVertexXiFourierTerm lam n alpha) -
          q * ∑' n : Nat, sixVertexXiRootConvolutionTerm lam n alpha := by
    have hpoint : (fun n : Nat =>
        sixVertexFourierRootDensityTerm lam n alpha) =
      (fun n : Nat => sixVertexXiFourierTerm lam n alpha -
        q * sixVertexXiRootConvolutionTerm lam n alpha) := by
      funext n
      exact (sixVertexXiTerm_sub_convolutionTerm_eq_rootDensityTerm
        lam n alpha).symm
    rw [hpoint]
    have hsum := hXi.hasSum.sub hqConv.hasSum
    rw [hsum.tsum_eq, tsum_mul_left]
  rw [intervalIntegral_XiFourier_mul_rootDensity hlam alpha]
  unfold sixVertexFourierRootDensity sixVertexXiFourier
  dsimp [q] at hseries ⊢
  rw [hseries]
  field_simp [Real.pi_ne_zero]
  ring

end
end StatMech.FrontierD
