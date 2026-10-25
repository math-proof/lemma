/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronDensityBoundConstant_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexCanonicalPerronDensityBoundConstant c := by
  unfold sixVertexCanonicalPerronDensityBoundConstant
  have hbase := sixVertexCanonicalPerronLipschitzBase_nonneg hc
  positivity

theorem eventually_sixVertexCanonicalPerronBound_mul_gauge_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalPerronRegularizedBound hc k *
          sixVertexCanonicalDensityPerronGauge hc k ≤
        sixVertexCanonicalPerronDensityBoundConstant c /
          (sixVertexPerronGaugeStage hc k : Real) := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc,
    eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow hc]
      with k hk hGauge
  let s : Real := sixVertexPerronGaugeStage hc k
  let base := sixVertexCanonicalPerronLipschitzBase c
  let D : Real := (1 / 2 : Real) * |Real.log (c ^ 4)| +
    base * Real.pi
  let A : Real := 2 + Real.pi
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hbase : 0 ≤ base :=
    sixVertexCanonicalPerronLipschitzBase_nonneg hc
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs8 : s ≤ s ^ 8 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 8 by omega)
  have hs5 : s ^ 5 ≤ s ^ 8 :=
    pow_le_pow_right₀ hsone (show 5 ≤ 8 by omega)
  have hB : sixVertexCanonicalPerronRegularizedBound hc k ≤
      D + A * s ^ 4 := by
    dsimp only [sixVertexCanonicalPerronRegularizedBound]
    rw [coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule hc
      (show 0 < sixVertexPerronGaugeStage hc k by omega)]
    have hzero :=
      abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule hc hk
    dsimp [s, base, D, A] at hzero ⊢
    nlinarith [mul_nonneg
      (sixVertexCanonicalPerronLipschitzBase_nonneg hc) Real.pi_pos.le]
  have hGaugeNonneg : 0 ≤ sixVertexCanonicalDensityPerronGauge hc k :=
    norm_nonneg _
  have hfirst :
      sixVertexCanonicalPerronRegularizedBound hc k *
          sixVertexCanonicalDensityPerronGauge hc k ≤
        (D + A * s ^ 4) * (1 / s ^ 8) := by
    calc
      _ ≤ (D + A * s ^ 4) *
          sixVertexCanonicalDensityPerronGauge hc k :=
        mul_le_mul_of_nonneg_right hB hGaugeNonneg
      _ ≤ (D + A * s ^ 4) * (1 / s ^ 8) := by
        gcongr
  have hsecond : (D + A * s ^ 4) * (1 / s ^ 8) ≤
      (D + A) / s := by
    rw [div_eq_mul_inv]
    field_simp [hs.ne']
    have hone7 : (1 : Real) ≤ s ^ 7 := by
      simpa using pow_le_pow_right₀ hsone (show 0 ≤ 7 by omega)
    have hs47 : s ^ 4 ≤ s ^ 7 :=
      pow_le_pow_right₀ hsone (show 4 ≤ 7 by omega)
    have hDscale : D ≤ D * s ^ 7 := by
      nlinarith [mul_le_mul_of_nonneg_left hone7 hD]
    have hAscale : A * s ^ 4 ≤ A * s ^ 7 :=
      mul_le_mul_of_nonneg_left hs47 hA
    calc
      D + A * s ^ 4 ≤ D * s ^ 7 + A * s ^ 7 :=
        add_le_add hDscale hAscale
      _ = s ^ 7 * (D + A) := by ring
  exact hfirst.trans (by
    simpa [sixVertexCanonicalPerronDensityBoundConstant, D, A, base]
      using hsecond)

theorem tendsto_sixVertexCanonicalPerronBound_mul_gauge
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k => sixVertexCanonicalPerronRegularizedBound hc k *
      sixVertexCanonicalDensityPerronGauge hc k) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper := hstageReal.const_div_atTop
    (sixVertexCanonicalPerronDensityBoundConstant c)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact mul_nonneg (by
      unfold sixVertexCanonicalPerronRegularizedBound
      positivity) (norm_nonneg _)
  · exact eventually_sixVertexCanonicalPerronBound_mul_gauge_le hc
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronDensityError
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalPerronRegularizedBound hc k *
        (sixVertexCanonicalDensityPerronGauge hc k /
          ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c)) * (2 * Real.pi))
      atTop (nhds 0) := by
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have h := ((tendsto_sixVertexCanonicalPerronBound_mul_gauge hc).div_const
    wmin).mul_const (2 * Real.pi)
  convert h using 1
  · funext k
    dsimp [wmin]
    ring
  · norm_num

theorem tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexCanonicalDensityPerronEmpiricalObservable hc
          (sixVertexRegularizedBetheLogKernel c
            (sixVertexCanonicalPerronLogEpsilon hc k)) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k)
      atTop (nhds 0) := by
  obtain ⟨lower, hlower, hdensity⟩ :=
    eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc
  let qerr : Nat → Real := fun k =>
    (sixVertexRegularizedBetheLogLipschitzConstant c
        (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
      (2 * Real.pi)
  let derr : Nat → Real := fun k =>
    sixVertexCanonicalPerronRegularizedBound hc k *
      (sixVertexCanonicalDensityPerronGauge hc k /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) * (2 * Real.pi)
  have hq : Tendsto qerr atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalPerronQuadratureError hc hlower
  have hd : Tendsto derr atTop (nhds 0) := by
    exact tendsto_sixVertexCanonicalPerronDensityError hc
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero' (g := fun k => qerr k + derr k)
  · filter_upwards [] with k
    exact abs_nonneg _
  · filter_upwards [hdensity,
      eventually_sixVertexCanonicalPerronLogEpsilon_pos hc]
      with k hkDensity hkEpsilon
    exact abs_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral_le
      hc hlower hkDensity hkEpsilon
  · simpa using hq.add hd


theorem tendsto_sixVertexCanonicalPerronRootAverage_sub_regularizedIntegral
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
        sixVertexCanonicalPerronRegularizedIntegral hc k)
      atTop (nhds 0) := by
  have hroot :=
    tendsto_sixVertexCanonicalPerronRootAverage_sub_regularized hc
  have hemp :=
    tendsto_sixVertexCanonicalPerronRegularizedEmpirical_sub_integral hc
  convert hroot.add hemp using 1
  · funext k
    ring
  · norm_num

end
end StatMech.FrontierD
