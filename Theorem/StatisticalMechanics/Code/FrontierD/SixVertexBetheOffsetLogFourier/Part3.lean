/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier.Part3


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem intervalIntegral_sixVertexRegularizedRapidityLogDerivative_mul_offset
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    (∫ alpha in -Real.pi..Real.pi,
      sixVertexRegularizedRapidityLogDerivative lam epsilon alpha *
        sixVertexOffsetRapidityProfile lam alpha) =
      sixVertexOffsetLogFourierDampedValue lam
        (sixVertexRegularizedRapidityRadius lam epsilon) := by
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  let L := (sixVertexOffsetRapidityLipschitzNNReal lam : Real) * Real.pi
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hL : 0 <= L := by dsimp [L]; positivity
  have hprofile (alpha : Real)
      (halpha : alpha ∈ Set.uIcc (-Real.pi) Real.pi) :
      |sixVertexOffsetRapidityProfile lam alpha| <= L := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at halpha
    have hlip := (lipschitzWith_sixVertexOffsetRapidityProfile hlam).dist_le_mul
      alpha 0
    have hzero : sixVertexOffsetRapidityProfile lam 0 = 0 := by
      simp [sixVertexOffsetRapidityProfile, sixVertexOffsetCorrectionTerm]
    rw [Real.dist_eq, Real.dist_eq, hzero, sub_zero, sub_zero] at hlip
    exact hlip.trans (mul_le_mul_of_nonneg_left (abs_le.2 halpha)
      (NNReal.coe_nonneg _))
  have hmajor : Summable (fun n : Nat =>
      (q ^ (n + 1) + r ^ (n + 1)) * L) :=
    ((summable_rapidityLogDerivative_majorant hlam hepsilon).mul_right L)
  have hnorm : Summable (fun n : Nat =>
      ‖(regularizedRapidityLogDerivativeMulOffsetContinuous
        lam epsilon hlam n).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (mul_nonneg
      (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _)) hL)]
    intro alpha
    change |sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n
      (alpha : Real) * sixVertexOffsetRapidityProfile lam alpha| <= _
    rw [abs_mul]
    have hterm :
        |sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha| <=
          q ^ (n + 1) + r ^ (n + 1) := by
      unfold sixVertexRegularizedRapidityLogDerivativeTerm
      dsimp only [q, r]
      rw [abs_mul]
      have hdiff : |q ^ (n + 1) - r ^ (n + 1)| <=
          q ^ (n + 1) + r ^ (n + 1) := by
        have h := abs_sub (q ^ (n + 1)) (r ^ (n + 1))
        rw [abs_pow, abs_pow, abs_of_pos hq.1, abs_of_pos hr.1] at h
        exact h
      simpa only [mul_one, q, r] using mul_le_mul hdiff (Real.abs_sin_le_one _)
        (abs_nonneg _) (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _))
    exact mul_le_mul hterm (hprofile alpha alpha.property)
      (abs_nonneg _) (add_nonneg (pow_nonneg hq.1.le _) (pow_nonneg hr.1.le _))
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have htermIntegral (n : Nat) :
      (∫ alpha in -Real.pi..Real.pi,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha) =
        sixVertexOffsetLogFourierDampedTerm lam r n := by
    have hsine := sixVertexOffsetRapidityProfile_sineCoefficient hlam
      (show 0 < n + 1 by omega)
    have hsine' :
        (∫ alpha in -Real.pi..Real.pi,
          sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((n + 1 : Real) * alpha)) =
          (-1 : Real) ^ (n + 1) *
            Real.tanh ((n + 1 : Real) * lam) / (n + 1 : Real) := by
      have hm : (n + 1 : Real) ≠ 0 := by positivity
      field_simp [Real.pi_ne_zero] at hsine
      apply (eq_div_iff hm).2
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hsine
    unfold sixVertexRegularizedRapidityLogDerivativeTerm
      sixVertexOffsetLogFourierDampedTerm
    dsimp only [q, r]
    rw [show (fun alpha : Real =>
        (q ^ (n + 1) - r ^ (n + 1)) *
          Real.sin ((n + 1 : Real) * alpha) *
            sixVertexOffsetRapidityProfile lam alpha) =
        fun alpha => (q ^ (n + 1) - r ^ (n + 1)) *
          (sixVertexOffsetRapidityProfile lam alpha *
            Real.sin ((n + 1 : Real) * alpha)) by
      funext alpha; ring,
      intervalIntegral.integral_const_mul, hsine']
    ring
  unfold sixVertexRegularizedRapidityLogDerivative
    sixVertexOffsetLogFourierDampedValue
  rw [show (fun alpha : Real =>
      (∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha) *
          sixVertexOffsetRapidityProfile lam alpha) =
      fun alpha => ∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha by
    funext alpha
    exact tsum_mul_right.symm]
  calc
    (∫ alpha in -Real.pi..Real.pi, ∑' n : Nat,
        sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
          sixVertexOffsetRapidityProfile lam alpha) =
        ∑' n : Nat, ∫ alpha in -Real.pi..Real.pi,
          sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha *
            sixVertexOffsetRapidityProfile lam alpha := by
      simpa [regularizedRapidityLogDerivativeMulOffsetContinuous] using hswap.symm
    _ = ∑' n : Nat, sixVertexOffsetLogFourierDampedTerm lam r n := by
      apply tsum_congr
      exact htermIntegral

end
end StatMech.FrontierD
