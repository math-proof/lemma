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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem norm_sixVertexOffsetSourceCorrectionTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetSourceCorrectionTerm lam n alpha‖ <=
      2 * Real.exp (-2 * lam) ^ (n + 1) := by
  rw [sixVertexOffsetSourceCorrectionTerm, Real.norm_eq_abs, abs_mul, abs_div,
    abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : Real) <= 2),
    abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (Real.exp_pos _),
    abs_of_pos (by positivity : (0 : Real) < (n + 1 : Real)), mul_one]
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
          (n + 1 : Real) * |Real.sin ((n + 1 : Real) * alpha)| <=
        2 * Real.exp (-2 * ((n + 1 : Real) * lam)) := by
      have hn : 1 <= (n + 1 : Real) := by norm_num
      have hdiv : 2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
          (n + 1 : Real) <=
          2 * Real.exp (-2 * ((n + 1 : Real) * lam)) := by
        exact div_le_self (by positivity) hn
      nlinarith [mul_le_mul_of_nonneg_left hsin
        (by positivity : 0 <=
          2 * Real.exp (-2 * ((n + 1 : Real) * lam)) /
            (n + 1 : Real))]
    _ = 2 * Real.exp (-2 * lam) ^ (n + 1) := by
      rw [<- Real.exp_nat_mul]
      congr 2
      push_cast
      ring

theorem summable_sixVertexOffsetSourceCorrectionTerm
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    Summable (fun n => sixVertexOffsetSourceCorrectionTerm lam n alpha) := by
  have hq0 : 0 <= Real.exp (-2 * lam) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * lam) < 1 := by
    rw [<- Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmajor : Summable (fun n : Nat =>
      2 * Real.exp (-2 * lam) ^ (n + 1)) :=
    ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left 2
  exact hmajor.of_norm_bounded
    (fun n => norm_sixVertexOffsetSourceCorrectionTerm_le lam n alpha)

theorem continuous_sixVertexOffsetSourceRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexOffsetSourceRapidityProfile lam) := by
  unfold sixVertexOffsetSourceRapidityProfile
  apply Continuous.add (by fun_prop)
  apply continuous_tsum
  · intro n
    unfold sixVertexOffsetSourceCorrectionTerm
    fun_prop
  · exact (summable_sixVertexFourierRootDensityMajorant (by linarith :
      0 < 2 * lam))
  · intro n alpha
    simpa [sixVertexFourierRootDensityMajorant] using
      norm_sixVertexOffsetSourceCorrectionTerm_le lam n alpha

theorem hasDerivAt_sixVertexOffsetSourceCorrectionTerm
    (lam : Real) (n : Nat) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceCorrectionTerm lam n)
      (sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
  unfold sixVertexOffsetSourceCorrectionTerm
    sixVertexOffsetSourceCorrectionDerivativeTerm
  have hsin : HasDerivAt
      (fun x : Real => Real.sin ((n + 1 : Real) * x))
      ((n + 1 : Real) * Real.cos ((n + 1 : Real) * alpha)) alpha := by
    convert Real.hasDerivAt_sin ((n + 1 : Real) * alpha) |>.comp alpha
      ((hasDerivAt_id alpha).const_mul (n + 1 : Real)) using 1 <;> ring
  convert hsin.const_mul
    (-2 * (-1 : Real) ^ (n + 1) *
      Real.exp (-2 * ((n + 1 : Real) * lam)) / (n + 1 : Real)) using 1
  field_simp [show (n + 1 : Real) ≠ 0 by positivity] <;> ring

theorem norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le
    (lam : Real) (n : Nat) (alpha : Real) :
    ‖sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha‖ <=
      sixVertexFourierRootDensityMajorant (2 * lam) n := by
  unfold sixVertexOffsetSourceCorrectionDerivativeTerm
    sixVertexFourierRootDensityMajorant
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : (0 : Real) <= 2), abs_pow, abs_neg,
    abs_one, one_pow, abs_of_pos (Real.exp_pos _)]
  have hcos : |Real.cos ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hexp :
      Real.exp (-2 * ((n + 1 : Real) * lam)) =
        Real.exp (-2 * lam) ^ (n + 1) := by
    rw [<- Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    2 * 1 * Real.exp (-2 * lam) ^ (n + 1) *
        |Real.cos ((n + 1 : Real) * alpha)| <=
      (2 * 1 * Real.exp (-2 * lam) ^ (n + 1)) * 1 :=
        mul_le_mul_of_nonneg_left hcos (by positivity)
    _ = 2 * Real.exp (-(2 * lam)) ^ (n + 1) := by ring

theorem hasDerivAt_sixVertexOffsetSourceRapidityProfile
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceRapidityProfile lam)
      (-1 + ∑' n : Nat,
        sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
  have hseries : HasDerivAt
      (fun x => ∑' n : Nat, sixVertexOffsetSourceCorrectionTerm lam n x)
      (∑' n : Nat,
        sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) alpha := by
    apply hasDerivAt_tsum
      (u := sixVertexFourierRootDensityMajorant (2 * lam))
      (g' := sixVertexOffsetSourceCorrectionDerivativeTerm lam)
      (y₀ := 0)
    · exact summable_sixVertexFourierRootDensityMajorant (by linarith)
    · intro n x
      exact hasDerivAt_sixVertexOffsetSourceCorrectionTerm lam n x
    · intro n x
      exact norm_sixVertexOffsetSourceCorrectionDerivativeTerm_le lam n x
    · simpa [sixVertexOffsetSourceCorrectionTerm] using
        (summable_zero : Summable (fun _n : Nat => (0 : Real)))
  unfold sixVertexOffsetSourceRapidityProfile
  convert (hasDerivAt_id alpha).neg.add hseries using 1 <;> ring

theorem sixVertexOffsetSourceCorrectionDerivativeTerm_eq
    (lam : Real) (n : Nat) (alpha : Real) :
    sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha =
      -sixVertexXiFourierTerm (2 * lam) n (alpha - Real.pi) := by
  unfold sixVertexOffsetSourceCorrectionDerivativeTerm
    sixVertexXiFourierTerm
  have hcast : (n + 1 : Real) = ((n + 1 : Nat) : Real) := by norm_num
  rw [hcast, mul_sub, Real.cos_sub, Real.cos_nat_mul_pi,
    Real.sin_nat_mul_pi]
  push_cast
  ring

theorem sixVertexXiFourier_add_pi_eq_sub_pi
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexXiFourier lam (alpha + Real.pi) =
      sixVertexXiFourier lam (alpha - Real.pi) := by
  rw [sixVertexXiFourier_eq hlam, sixVertexXiFourier_eq hlam]
  congr 2
  rw [show alpha + Real.pi = (alpha - Real.pi) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexOffsetSourceRapidityProfile lam)
      (-sixVertexXiFourier (2 * lam) (alpha - Real.pi)) alpha := by
  have h := hasDerivAt_sixVertexOffsetSourceRapidityProfile hlam alpha
  convert h using 1
  unfold sixVertexXiFourier
  rw [show (∑' n : Nat,
      sixVertexOffsetSourceCorrectionDerivativeTerm lam n alpha) =
      -(∑' n : Nat,
        sixVertexXiFourierTerm (2 * lam) n (alpha - Real.pi)) by
    rw [<- tsum_neg]
    apply tsum_congr
    intro n
    exact sixVertexOffsetSourceCorrectionDerivativeTerm_eq lam n alpha]
  ring

theorem hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    HasDerivAt
      (fun t => sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) t))
      (-(sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
          (alpha + Real.pi) +
        sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
          (alpha - Real.pi)) / 2) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let k := sixVertexRapidityMomentum lam
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hk := hasDerivAt_sixVertexRapidityMomentum hlam alpha
  have hthetaLeft : HasDerivAt (fun x => sixVertexTheta c x (-Real.pi))
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-Real.pi) /
        sixVertexThetaDerivativeDenominator c (k alpha) (-Real.pi)) (k alpha) := by
    simpa [sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc (k alpha) (-Real.pi)
  have hthetaRight : HasDerivAt (fun x => sixVertexTheta c x Real.pi)
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c Real.pi /
        sixVertexThetaDerivativeDenominator c (k alpha) Real.pi) (k alpha) := by
    simpa [sixVertexBetheIntegratingFactor,
      sixVertexThetaDerivativeDenominator] using
      hasDerivAt_sixVertexTheta_left hc (k alpha) Real.pi
  have hleft := hthetaLeft.comp alpha hk
  have hright := hthetaRight.comp alpha hk
  have hweight : sixVertexXiFourier lam alpha =
      sixVertexRootDensityWeight c (k alpha) := by
    exact (sixVertexRootDensityWeight_rapidityMomentum hc alpha).symm
  have hnegPi : -Real.pi = k (-Real.pi) := by
    exact (sixVertexRapidityMomentum_neg_pi hlam).symm
  have hpi : Real.pi = k Real.pi := by
    exact (sixVertexRapidityMomentum_pi hlam).symm
  have hleftDeriv :
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-Real.pi) /
          sixVertexThetaDerivativeDenominator c (k alpha) (-Real.pi)) *
          sixVertexXiFourier lam alpha =
        -sixVertexXiFourier (2 * lam) (alpha + Real.pi) := by
    have hkernel := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
      hc (k alpha) (-Real.pi)
    have hkernelRapid : sixVertexRootDensityKernel c (k alpha) (-Real.pi) =
        sixVertexXiFourier (2 * lam) (alpha - (-Real.pi)) := by
      calc
        _ = sixVertexRootDensityKernel c (k alpha) (k (-Real.pi)) :=
          congrArg (sixVertexRootDensityKernel c (k alpha)) hnegPi
        _ = _ := sixVertexRootDensityKernel_rapidityMomentum hc alpha (-Real.pi)
    rw [hweight]
    calc
      _ = -sixVertexRootDensityKernel c (k alpha) (-Real.pi) := by
        rw [hkernel]
        ring
      _ = -sixVertexXiFourier (2 * lam) (alpha - (-Real.pi)) := by
        rw [hkernelRapid]
      _ = _ := by ring_nf
  have hrightDeriv :
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c Real.pi /
          sixVertexThetaDerivativeDenominator c (k alpha) Real.pi) *
          sixVertexXiFourier lam alpha =
        -sixVertexXiFourier (2 * lam) (alpha - Real.pi) := by
    have hkernel := sixVertexRootDensityKernel_eq_neg_weight_mul_leftDerivative
      hc (k alpha) Real.pi
    have hkernelRapid : sixVertexRootDensityKernel c (k alpha) Real.pi =
        sixVertexXiFourier (2 * lam) (alpha - Real.pi) := by
      calc
        _ = sixVertexRootDensityKernel c (k alpha) (k Real.pi) :=
          congrArg (sixVertexRootDensityKernel c (k alpha)) hpi
        _ = _ := sixVertexRootDensityKernel_rapidityMomentum hc alpha Real.pi
    rw [hweight]
    calc
      _ = -sixVertexRootDensityKernel c (k alpha) Real.pi := by
        rw [hkernel]
        ring
      _ = _ := by rw [hkernelRapid]
  unfold sixVertexContinuousOffsetSource
  convert hleft.add hright |>.div_const 2 using 1 <;>
    dsimp only [k, lam] <;>
    rw [hleftDeriv, hrightDeriv] <;>
    ring

theorem hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
    {c : Real} (hc : 2 < c) (alpha : Real) :
    HasDerivAt
      (fun t => sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) t))
      (-sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c)
        (alpha - Real.pi)) alpha := by
  have h := hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum
    hc alpha
  convert h using 1
  rw [sixVertexXiFourier_add_pi_eq_sub_pi
    (by linarith [sixVertexAntiferroelectricLambda_pos hc] :
      0 < 2 * sixVertexAntiferroelectricLambda c) alpha]
  ring


theorem sixVertexContinuousOffsetSource_rapidityMomentum
    {c : Real} (hc : 2 < c) (alpha : Real) :
    sixVertexContinuousOffsetSource c
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) =
      sixVertexOffsetSourceRapidityProfile
        (sixVertexAntiferroelectricLambda c) alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  let f : Real -> Real := fun t =>
    sixVertexContinuousOffsetSource c (sixVertexRapidityMomentum lam t)
  let g : Real -> Real := sixVertexOffsetSourceRapidityProfile lam
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hf : Differentiable Real f := by
    intro t
    exact (hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
      hc t).differentiableAt
  have hg : Differentiable Real g := by
    intro t
    exact (hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi hlam t)
      |>.differentiableAt
  have hderiv (t : Real) : fderiv Real f t = fderiv Real g t := by
    rw [(hasDerivAt_sixVertexContinuousOffsetSource_rapidityMomentum_eq_Xi
      hc t).hasFDerivAt.fderiv,
      (hasDerivAt_sixVertexOffsetSourceRapidityProfile_eq_Xi hlam t)
        |>.hasFDerivAt.fderiv]
  have hfzero : f 0 = 0 := by
    have hodd := odd_sixVertexContinuousOffsetSource c 0
    have hkzero : sixVertexRapidityMomentum lam 0 = 0 := by
      simp [sixVertexRapidityMomentum]
    dsimp [f]
    rw [hkzero]
    have hodd' : sixVertexContinuousOffsetSource c 0 =
        -sixVertexContinuousOffsetSource c 0 := by
      simpa only [neg_zero] using hodd
    linarith
  have hgzero : g 0 = 0 := by
    simp [g, sixVertexOffsetSourceRapidityProfile,
      sixVertexOffsetSourceCorrectionTerm]
  have hfg : f = g := eq_of_fderiv_eq hf hg hderiv 0 (hfzero.trans hgzero.symm)
  exact congrFun hfg alpha


end
end StatMech.FrontierD
