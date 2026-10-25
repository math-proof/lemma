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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier.Part2


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem summable_rapidityLogDerivative_majorant
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon) :
    Summable (fun n : Nat =>
      sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
        sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)) := by
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  exact ((summable_geometric_of_lt_one hq.1.le hq.2).comp_injective
      Nat.succ_injective).add
    ((summable_geometric_of_lt_one hr.1.le hr.2).comp_injective
      Nat.succ_injective)

theorem summable_sixVertexRegularizedRapidityLogDerivativeTerm
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    Summable (fun n : Nat =>
      sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha) := by
  apply (summable_rapidityLogDerivative_majorant hlam hepsilon).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs]
  unfold sixVertexRegularizedRapidityLogDerivativeTerm
  dsimp only
  rw [abs_mul]
  have hqpow : 0 <= sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) :=
    pow_nonneg (sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam).1.le _
  have hrpow : 0 <=
      sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1) :=
    pow_nonneg
      (sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon).1.le _
  have hdiff :
      |sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) -
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)| <=
        sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1) := by
    simpa [abs_of_nonneg hqpow, abs_of_nonneg hrpow] using
      (abs_sub (sixVertexFreeEnergyRapidityRadius lam ^ (n + 1))
        (sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)))
  have hsin : |Real.sin ((n + 1 : Real) * alpha)| <= 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  calc
    |sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) -
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)| *
        |Real.sin ((n + 1 : Real) * alpha)| <=
        (sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) +
          sixVertexRegularizedRapidityRadius lam epsilon ^ (n + 1)) * 1 :=
      mul_le_mul hdiff hsin (abs_nonneg _) (add_nonneg hqpow hrpow)
    _ = _ := mul_one _

theorem hasDerivAt_sixVertexLogCosineSeries
    {r : Real} (hr : |r| < 1) (alpha : Real) :
    HasDerivAt (sixVertexLogCosineSeries r)
      (∑' n : Nat, -r ^ (n + 1) *
        Real.sin ((n + 1 : Real) * alpha)) alpha := by
  let g : Nat -> Real -> Real := fun n x =>
    r ^ (n + 1) * Real.cos ((n + 1 : Real) * x) / (n + 1 : Real)
  let g' : Nat -> Real -> Real := fun n x =>
    -r ^ (n + 1) * Real.sin ((n + 1 : Real) * x)
  let u : Nat -> Real := fun n => |r| ^ (n + 1)
  have hu : Summable u :=
    (summable_geometric_of_lt_one (abs_nonneg r) hr).comp_injective
      Nat.succ_injective
  have hg (n : Nat) (x : Real) : HasDerivAt (g n) (g' n x) x := by
    have hlin : HasDerivAt (fun y : Real => (n + 1 : Real) * y)
        (n + 1 : Real) x := by
      simpa using (hasDerivAt_id x).const_mul (n + 1 : Real)
    have h := ((Real.hasDerivAt_cos ((n + 1 : Real) * x)).comp x hlin).const_mul
      (r ^ (n + 1) / (n + 1 : Real))
    have hm : (n + 1 : Real) ≠ 0 := by positivity
    convert h using 1
    · funext y
      dsimp [g]
      ring
    · dsimp [g']
      field_simp [hm]
  have hg' (n : Nat) (x : Real) : ‖g' n x‖ <= u n := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
    have hs : |Real.sin ((n + 1 : Real) * x)| <= 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (pow_nonneg (abs_nonneg r) _)
  have hg0 : Summable (fun n => g n 0) := by
    apply hu.of_norm_bounded
    intro n
    dsimp [g, u]
    rw [mul_zero, Real.cos_zero, mul_one]
    have hden : 1 <= |(n + 1 : Real)| := by
      rw [abs_of_pos (by positivity)]
      norm_num
    calc
      |r ^ (n + 1) / (n + 1 : Real)| =
          |r ^ (n + 1)| / |(n + 1 : Real)| := abs_div _ _
      _ = |r| ^ (n + 1) / |(n + 1 : Real)| := by rw [abs_pow]
      _ <= |r| ^ (n + 1) :=
        div_le_self (pow_nonneg (abs_nonneg r) _) hden
  have h := hasDerivAt_tsum (u := u) (g := g) (g' := g')
    hu hg hg' hg0 alpha
  change HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n alpha) alpha
  exact h

theorem summable_logCosineDerivative
    {r : Real} (hr : r ∈ Set.Ioo 0 1) (alpha : Real) :
    Summable (fun n : Nat => -r ^ (n + 1) *
      Real.sin ((n + 1 : Real) * alpha)) := by
  have hgeom := (summable_geometric_of_lt_one hr.1.le hr.2).comp_injective
    Nat.succ_injective
  apply hgeom.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hr.1.le _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_one _) (pow_nonneg hr.1.le _)

theorem hasDerivAt_sixVertexRegularizedRapidityLogSeries
    {lam epsilon : Real} (hlam : 0 < lam) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    HasDerivAt
      (fun beta =>
        sixVertexRegularizedRapidityConstant lam epsilon +
          sixVertexLogCosineSeries
            (sixVertexRegularizedRapidityRadius lam epsilon) beta -
          sixVertexLogCosineSeries
            (sixVertexFreeEnergyRapidityRadius lam) beta)
      (sixVertexRegularizedRapidityLogDerivative lam epsilon alpha) alpha := by
  have hq := sixVertexFreeEnergyRapidityRadius_mem_Ioo hlam
  have hr := sixVertexRegularizedRapidityRadius_mem_Ioo hlam hepsilon
  have hR := hasDerivAt_sixVertexLogCosineSeries
    (by rw [abs_of_pos hr.1]; exact hr.2) alpha
  have hQ := hasDerivAt_sixVertexLogCosineSeries
    (by rw [abs_of_pos hq.1]; exact hq.2) alpha
  have h := (hR.const_add
    (sixVertexRegularizedRapidityConstant lam epsilon)).sub hQ
  convert h using 1
  unfold sixVertexRegularizedRapidityLogDerivative
    sixVertexRegularizedRapidityLogDerivativeTerm
  have hRsum := summable_logCosineDerivative hr alpha
  have hQsum := summable_logCosineDerivative hq alpha
  rw [<- hRsum.tsum_sub hQsum]
  apply tsum_congr
  intro n
  ring

theorem sixVertexRegularizedBetheLogDerivative_rapidityMomentum
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon)
    (alpha : Real) :
    sixVertexRegularizedBetheLogNormDerivative c epsilon
        (sixVertexRapidityMomentum
          (sixVertexAntiferroelectricLambda c) alpha) *
      sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha =
    sixVertexRegularizedRapidityLogDerivative
      (sixVertexAntiferroelectricLambda c) epsilon alpha := by
  let lam := sixVertexAntiferroelectricLambda c
  have hlam : 0 < lam := sixVertexAntiferroelectricLambda_pos hc
  have hleft := (hasDerivAt_sixVertexRegularizedBetheLogKernel hc hepsilon).comp
    alpha (hasDerivAt_sixVertexRapidityMomentum hlam alpha)
  have hright := hasDerivAt_sixVertexRegularizedRapidityLogSeries
    hlam hepsilon alpha
  have hfun : (fun beta => sixVertexRegularizedBetheLogKernel c epsilon
        (sixVertexRapidityMomentum lam beta)) =
      fun beta =>
        sixVertexRegularizedRapidityConstant lam epsilon +
          sixVertexLogCosineSeries
            (sixVertexRegularizedRapidityRadius lam epsilon) beta -
          sixVertexLogCosineSeries
            (sixVertexFreeEnergyRapidityRadius lam) beta := by
    funext beta
    exact sixVertexRegularizedBetheLogKernel_rapidityMomentum_eq_series
      hc hepsilon beta
  change HasDerivAt
    (fun beta => sixVertexRegularizedBetheLogKernel c epsilon
      (sixVertexRapidityMomentum lam beta)) _ alpha at hleft
  rw [hfun] at hleft
  exact hright.unique hleft |>.symm

end
end StatMech.FrontierD
