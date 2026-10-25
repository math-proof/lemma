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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem intervalIntegral_XiFourier_mul_offsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourier (2 * lam) (alpha - beta) *
        sixVertexOffsetRapidityProfile lam beta) =
      ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha := by
  have h2lam : 0 < 2 * lam := by linarith
  let K : TopologicalSpace.Compacts Real :=
    ⟨Set.uIcc (-Real.pi) Real.pi, isCompact_uIcc⟩
  let tauMap : C(Real, Real) :=
    ⟨sixVertexOffsetRapidityProfile lam,
      continuous_sixVertexOffsetRapidityProfile hlam⟩
  let B : Real := ‖tauMap.restrict K‖
  have hB : 0 <= B := norm_nonneg _
  have hmajor : Summable (fun n : Nat =>
      sixVertexFourierRootDensityMajorant (2 * lam) n * B) :=
    (summable_sixVertexFourierRootDensityMajorant h2lam).mul_right B
  have hnorm : Summable (fun n : Nat =>
      ‖(XiFourierTermMulOffsetRapidityProfileContinuous
        hlam n alpha).restrict K‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hmajor
    rw [ContinuousMap.norm_le _ (mul_nonneg
      (by unfold sixVertexFourierRootDensityMajorant; positivity) hB)]
    intro beta
    change |sixVertexXiFourierTerm (2 * lam) n (alpha - (beta : Real)) *
        sixVertexOffsetRapidityProfile lam beta| <= _
    rw [abs_mul]
    apply mul_le_mul
    · simpa only [Real.norm_eq_abs] using
        norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - (beta : Real))
    · simpa only [Real.norm_eq_abs] using
        (tauMap.restrict K).norm_coe_le_norm beta
    · exact abs_nonneg _
    · unfold sixVertexFourierRootDensityMajorant
      positivity
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hnorm
  have hswap' :
      (∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) := by
    simpa only [XiFourierTermMulOffsetRapidityProfileContinuous] using hswap
  have htauZero :
      (∫ beta in -Real.pi..Real.pi,
        sixVertexOffsetRapidityProfile lam beta) = 0 :=
    intervalIntegral_neg_pi_pi_eq_zero_of_odd
      (odd_sixVertexOffsetRapidityProfile lam)
  have htauInt : IntervalIntegrable
      (sixVertexOffsetRapidityProfile lam) MeasureTheory.volume
      (-Real.pi) Real.pi :=
    (continuous_sixVertexOffsetRapidityProfile hlam).intervalIntegrable _ _
  have hseriesContinuous : Continuous (fun beta =>
      (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) := by
    apply Continuous.mul
    · apply continuous_tsum
      · intro n
        unfold sixVertexXiFourierTerm
        fun_prop
      · exact summable_sixVertexFourierRootDensityMajorant h2lam
      · intro n beta
        exact norm_sixVertexXiFourierTerm_le (2 * lam) n (alpha - beta)
    · exact continuous_sixVertexOffsetRapidityProfile hlam
  unfold sixVertexXiFourier
  rw [show (fun beta =>
      (1 + ∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
        sixVertexOffsetRapidityProfile lam beta) =
      fun beta => sixVertexOffsetRapidityProfile lam beta +
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta)) *
          sixVertexOffsetRapidityProfile lam beta by
    funext beta
    ring]
  rw [intervalIntegral.integral_add htauInt
      (hseriesContinuous.intervalIntegrable _ _), htauZero, zero_add]
  calc
    _ = ∫ beta in -Real.pi..Real.pi,
        (∑' n : Nat, sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta) := by
      apply intervalIntegral.integral_congr
      intro beta _
      exact tsum_mul_right.symm
    _ = ∑' n : Nat, ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := hswap'.symm
    _ = _ := by
      apply tsum_congr
      intro n
      exact intervalIntegral_XiFourierTerm_mul_offsetRapidityProfile
        hlam n alpha

theorem exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh (x : Real) :
    Real.exp (-2 * x) * (1 + Real.tanh x) = 1 - Real.tanh x := by
  rw [Real.tanh_eq]
  have hexp : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by positivity
  have hrel : Real.exp (-2 * x) * Real.exp x = Real.exp (-x) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  field_simp [hexp, hden]
  calc
    Real.exp (-(2 * x)) *
        (Real.exp x + Real.exp (-x) + (Real.exp x - Real.exp (-x))) =
      2 * (Real.exp (-2 * x) * Real.exp x) := by ring
    _ = 2 * Real.exp (-x) := by rw [hrel]
    _ = Real.exp x + Real.exp (-x) -
        (Real.exp x - Real.exp (-x)) := by ring

theorem sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexOffsetSourceCorrectionTerm lam n alpha -
        sixVertexOffsetConvolutionTerm lam n alpha =
      2 * Real.pi * sixVertexOffsetCorrectionTerm lam n alpha := by
  let m : Real := n + 1
  let x : Real := m * lam
  have hm : m ≠ 0 := by dsimp [m]; positivity
  have hidentity := exp_neg_two_mul_one_add_tanh_eq_one_sub_tanh x
  unfold sixVertexOffsetSourceCorrectionTerm
    sixVertexOffsetConvolutionTerm sixVertexOffsetCorrectionTerm
    sixVertexGapCorrectionTerm
  dsimp [m, x] at hidentity ⊢
  have hexp : Real.exp (-2 * ((n + 1 : Real) * lam)) *
      (1 + Real.tanh ((n + 1 : Real) * lam)) =
      1 - Real.tanh ((n + 1 : Real) * lam) := hidentity
  field_simp [Real.pi_ne_zero, hm]
  calc
    Real.exp (-(2 * (n + 1 : Real) * lam)) *
        Real.sin ((n + 1 : Real) * alpha) *
          (-1 - Real.tanh ((n + 1 : Real) * lam)) =
      -(Real.exp (-2 * ((n + 1 : Real) * lam)) *
          (1 + Real.tanh ((n + 1 : Real) * lam))) *
        Real.sin ((n + 1 : Real) * alpha) := by ring
    _ = -(1 - Real.tanh ((n + 1 : Real) * lam)) *
        Real.sin ((n + 1 : Real) * alpha) := by rw [hexp]
    _ = Real.sin ((n + 1 : Real) * alpha) *
        (Real.tanh ((n + 1 : Real) * lam) - 1) := by ring


theorem sixVertexOffsetRapidityProfile_integralEquation
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    2 * Real.pi * sixVertexOffsetRapidityProfile lam alpha =
      sixVertexOffsetSourceRapidityProfile lam alpha -
        ∫ beta in -Real.pi..Real.pi,
          sixVertexXiFourier (2 * lam) (alpha - beta) *
            sixVertexOffsetRapidityProfile lam beta := by
  rw [intervalIntegral_XiFourier_mul_offsetRapidityProfile hlam alpha]
  have hsource := summable_sixVertexOffsetSourceCorrectionTerm hlam alpha
  have hconv := summable_sixVertexOffsetConvolutionTerm hlam alpha
  have hdiff := hsource.tsum_sub hconv
  unfold sixVertexOffsetRapidityProfile sixVertexOffsetSourceRapidityProfile
  rw [show -alpha +
        (∑' n : Nat, sixVertexOffsetSourceCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha =
      -alpha + ((∑' n : Nat,
        sixVertexOffsetSourceCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetConvolutionTerm lam n alpha) by ring,
    <- hdiff]
  have hterm :
      (∑' n : Nat, (sixVertexOffsetSourceCorrectionTerm lam n alpha -
        sixVertexOffsetConvolutionTerm lam n alpha)) =
      ∑' n : Nat, 2 * Real.pi *
        sixVertexOffsetCorrectionTerm lam n alpha := by
    apply tsum_congr
    intro n
    exact sixVertexOffsetSourceCorrectionTerm_sub_convolutionTerm lam n alpha
  rw [hterm, tsum_mul_left]
  field_simp [Real.pi_ne_zero]


theorem intervalIntegral_continuousOffsetKernel_mul_fourier_pullback
    {c : Real} (hc : 2 < c) (alpha : Real) :
    (∫ y in -Real.pi..Real.pi,
      sixVertexContinuousOffsetKernel c
          (sixVertexRapidityMomentum
            (sixVertexAntiferroelectricLambda c) alpha) y *
        sixVertexContinuousOffsetFourier c hc y) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
            (alpha - beta) *
          sixVertexOffsetRapidityProfile
            (sixVertexAntiferroelectricLambda c) beta := by
  let lam := sixVertexAntiferroelectricLambda c
  let k := sixVertexRapidityMomentum lam
  let x := k alpha
  let g : Real -> Real := fun y =>
    sixVertexContinuousOffsetKernel c x y *
      sixVertexContinuousOffsetFourier c hc y
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hweight : Continuous (sixVertexRootDensityWeight c) := by
    unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
      sixVertexRootDensityScale
    fun_prop
  have hkernel : Continuous (sixVertexContinuousOffsetKernel c x) := by
    unfold sixVertexContinuousOffsetKernel
    exact (lipschitzWith_sixVertexRootDensityKernel_right hc x).continuous.div
      hweight (fun y => (sixVertexRootDensityWeight_pos hc y).ne')
  have hg : Continuous g :=
    hkernel.mul (continuous_sixVertexContinuousOffsetFourier hc)
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := -Real.pi) (b := Real.pi) (f := k)
    (f' := sixVertexXiFourier lam) (g := g)
    (fun beta _ => hasDerivAt_sixVertexRapidityMomentum hlam beta)
    (continuous_sixVertexXiFourier hlam).continuousOn hg
  have hkneg : k (-Real.pi) = -Real.pi :=
    sixVertexRapidityMomentum_neg_pi hlam
  have hkpi : k Real.pi = Real.pi :=
    sixVertexRapidityMomentum_pi hlam
  rw [hkneg, hkpi] at hsubst
  have hpulled :
      (∫ beta in -Real.pi..Real.pi,
        (g ∘ k) beta * sixVertexXiFourier lam beta) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * lam) (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := by
    apply intervalIntegral.integral_congr
    intro beta hbeta
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -Real.pi <= Real.pi)] at hbeta
    dsimp only [Function.comp_apply, g, x, k]
    unfold sixVertexContinuousOffsetKernel
    rw [sixVertexRootDensityKernel_rapidityMomentum hc,
      sixVertexRootDensityWeight_rapidityMomentum hc,
      sixVertexContinuousOffsetFourier_rapidityMomentum hc hbeta]
    have hXi : sixVertexXiFourier lam beta ≠ 0 :=
      (sixVertexXiFourier_pos hlam beta).ne'
    dsimp [lam] at hXi ⊢
    field_simp [hXi]
  change (∫ y in -Real.pi..Real.pi, g y) = _
  rw [<- hsubst, hpulled]


theorem sixVertexContinuousOffsetFourier_satisfiesEquation
    {c : Real} (hc : 2 < c) :
    SixVertexSatisfiesContinuousOffsetEquation c
      (sixVertexContinuousOffsetFourier c hc) := by
  intro x hx
  let lam := sixVertexAntiferroelectricLambda c
  let alpha := sixVertexMomentumRapidity lam
    (sixVertexAntiferroelectricLambda_pos hc) x
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hxalpha : sixVertexRapidityMomentum lam alpha = x := by
    exact sixVertexRapidityMomentum_momentumRapidity hlam hx
  have halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi := by
    dsimp [alpha, sixVertexMomentumRapidity]
    exact ((sixVertexRapidityMomentumOrderIso lam hlam).symm
      (Set.projIcc (-Real.pi) Real.pi
        (by linarith [Real.pi_pos]) x)).property
  have heq := sixVertexOffsetRapidityProfile_integralEquation hlam alpha
  have htau : sixVertexContinuousOffsetFourier c hc x =
      sixVertexOffsetRapidityProfile lam alpha := by
    rw [<- hxalpha]
    exact sixVertexContinuousOffsetFourier_rapidityMomentum hc halpha
  have hsource : sixVertexContinuousOffsetSource c x =
      sixVertexOffsetSourceRapidityProfile lam alpha := by
    rw [<- hxalpha]
    exact sixVertexContinuousOffsetSource_rapidityMomentum hc alpha
  have hintegral :
      (∫ y in -Real.pi..Real.pi,
        sixVertexContinuousOffsetKernel c x y *
          sixVertexContinuousOffsetFourier c hc y) =
      ∫ beta in -Real.pi..Real.pi,
        sixVertexXiFourier (2 * lam) (alpha - beta) *
          sixVertexOffsetRapidityProfile lam beta := by
    rw [<- hxalpha]
    exact intervalIntegral_continuousOffsetKernel_mul_fourier_pullback
      hc alpha
  rw [htau, hsource, hintegral]
  exact heq

end
end StatMech.FrontierD
