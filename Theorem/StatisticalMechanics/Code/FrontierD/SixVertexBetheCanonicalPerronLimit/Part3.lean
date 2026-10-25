/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronLipschitzBase_nonneg
    {c : Real} (hc : 2 < c) :
    0 ≤ sixVertexCanonicalPerronLipschitzBase c := by
  unfold sixVertexCanonicalPerronLipschitzBase
  exact div_nonneg (by nlinarith [sq_nonneg c]) (sq_nonneg _)

theorem coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule
    {c : Real} (hc : 2 < c) {k : Nat}
    (hstage : 0 < sixVertexPerronGaugeStage hc k) :
    (sixVertexRegularizedBetheLogLipschitzConstant c
        (sixVertexCanonicalPerronLogEpsilon hc k) : Real) =
      sixVertexCanonicalPerronLipschitzBase c +
        (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
  let s : Real := sixVertexPerronGaugeStage hc k
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast hstage
  let A : Real := (1 / 2 : Real) *
    ((2 * (c ^ 2 - 1)) / (c ^ 2 - 2) ^ 2 +
      2 / sixVertexCanonicalPerronLogEpsilon hc k)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hc1 : 0 ≤ 2 * (c ^ 2 - 1) := by nlinarith [sq_nonneg c]
    have heps : 0 < sixVertexCanonicalPerronLogEpsilon hc k := by
      unfold sixVertexCanonicalPerronLogEpsilon
      positivity
    exact mul_nonneg (by norm_num)
      (add_nonneg (div_nonneg hc1 (sq_nonneg _))
        (div_nonneg (by norm_num) heps.le))
  rw [sixVertexRegularizedBetheLogLipschitzConstant,
    Real.coe_toNNReal _ hA]
  change A = _
  dsimp [A, sixVertexCanonicalPerronLipschitzBase,
    sixVertexCanonicalPerronLogEpsilon, s]
  field_simp [hs.ne']

theorem abs_sixVertexRegularizedBetheLogKernel_zero_le_schedule
    {c : Real} (hc : 2 < c) {k : Nat}
    (hstage : 2 ≤ sixVertexPerronGaugeStage hc k) :
    |sixVertexRegularizedBetheLogKernel c
        (sixVertexCanonicalPerronLogEpsilon hc k) 0| ≤
      (1 / 2 : Real) * |Real.log (c ^ 4)| +
        2 * (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
  let s : Real := sixVertexPerronGaugeStage hc k
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hlogsNonneg : 0 ≤ Real.log s := Real.log_nonneg hsone
  have hlogsLe : Real.log s ≤ s := by
    have h := Real.log_le_sub_one_of_pos hs
    linarith
  have hsPow : s ≤ s ^ 4 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 4 by omega)
  have hepsLog :
      |Real.log (sixVertexCanonicalPerronLogEpsilon hc k)| ≤
        4 * s ^ 4 := by
    have hsne : s ≠ 0 := hs.ne'
    unfold sixVertexCanonicalPerronLogEpsilon
    change |Real.log ((1 : Real) / s ^ 4)| ≤ 4 * s ^ 4
    rw [Real.log_div one_ne_zero (pow_ne_zero 4 hsne), Real.log_one,
      zero_sub, abs_neg, Real.log_pow]
    rw [abs_mul, abs_of_nonneg hlogsNonneg]
    norm_num
    nlinarith
  have hnum : sixVertexBetheLogNumerator c 0 = c ^ 4 := by
    unfold sixVertexBetheLogNumerator
    rw [Real.cos_zero]
    ring
  have hden : sixVertexBetheLogDenominator 0 = 0 := by
    simp [sixVertexBetheLogDenominator]
  unfold sixVertexRegularizedBetheLogKernel
  rw [hnum, hden, zero_add]
  calc
    |(1 / 2 : Real) *
        (Real.log (c ^ 4) -
          Real.log (sixVertexCanonicalPerronLogEpsilon hc k))| =
        (1 / 2 : Real) *
          |Real.log (c ^ 4) -
            Real.log (sixVertexCanonicalPerronLogEpsilon hc k)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
    _ ≤ (1 / 2 : Real) *
        (|Real.log (c ^ 4)| +
          |Real.log (sixVertexCanonicalPerronLogEpsilon hc k)|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ (1 / 2 : Real) *
        (|Real.log (c ^ 4)| + 4 * s ^ 4) := by gcongr
    _ = (1 / 2 : Real) * |Real.log (c ^ 4)| + 2 *
        (sixVertexPerronGaugeStage hc k : Real) ^ 4 := by
      dsimp [s]
      ring

theorem eventually_sixVertexCanonicalPerronLipschitz_div_width_le
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) /
          (sixVertexFourWidth 0 k : Real) ≤
        (sixVertexCanonicalPerronLipschitzBase c + 1) /
          (sixVertexPerronGaugeStage hc k : Real) := by
  filter_upwards [eventually_two_le_sixVertexPerronGaugeStage hc] with k hk
  let s : Real := sixVertexPerronGaugeStage hc k
  let m : Real := k + 1
  let base := sixVertexCanonicalPerronLipschitzBase c
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast (show 0 < sixVertexPerronGaugeStage hc k by omega)
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact_mod_cast (show 1 ≤ sixVertexPerronGaugeStage hc k by omega)
  have hm : s ^ 8 ≤ m := by
    dsimp [s, m]
    exact_mod_cast sixVertexPerronGaugeStage_pow_eight_le hc k
  have hbase : 0 ≤ base :=
    sixVertexCanonicalPerronLipschitzBase_nonneg hc
  have hs8 : s ≤ s ^ 8 := by
    simpa using pow_le_pow_right₀ hsone (show 1 ≤ 8 by omega)
  have hs5 : s ^ 5 ≤ s ^ 8 :=
    pow_le_pow_right₀ hsone (show 5 ≤ 8 by omega)
  have hbaseScale : base * s ≤ base * s ^ 8 :=
    mul_le_mul_of_nonneg_left hs8 hbase
  have hnum : (base + s ^ 4) * s ≤ (base + 1) * m := by
    calc
      (base + s ^ 4) * s = base * s + s ^ 5 := by ring
      _ ≤ base * s ^ 8 + s ^ 8 := add_le_add hbaseScale hs5
      _ = (base + 1) * s ^ 8 := by ring
      _ ≤ (base + 1) * m :=
        mul_le_mul_of_nonneg_left hm (by positivity)
  rw [coe_sixVertexRegularizedBetheLogLipschitzConstant_schedule hc
    (show 0 < sixVertexPerronGaugeStage hc k by omega)]
  rw [sixVertexFourWidth]
  push_cast
  simp only [zero_add]
  change (base + s ^ 4) / (4 * m) ≤ (base + 1) / s
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [mul_nonneg (show 0 ≤ base + 1 by positivity)
    (show 0 ≤ m by positivity)]

theorem tendsto_sixVertexCanonicalPerronLipschitz_div_width
    {c : Real} (hc : 2 < c) :
    Tendsto (fun k =>
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) /
        (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper := hstageReal.const_div_atTop
    (sixVertexCanonicalPerronLipschitzBase c + 1)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact div_nonneg (NNReal.coe_nonneg _)
      (Nat.cast_nonneg _)
  · exact eventually_sixVertexCanonicalPerronLipschitz_div_width_le hc
  · exact hupper

theorem tendsto_sixVertexCanonicalPerronQuadratureError
    {c : Real} (hc : 2 < c) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun k =>
      (sixVertexRegularizedBetheLogLipschitzConstant c
          (sixVertexCanonicalPerronLogEpsilon hc k) : Real) *
        sixVertexFiniteRootDensityUniformBound c *
        (1 / ((sixVertexFourWidth 0 k : Real) * lower)) *
        (2 * Real.pi)) atTop (nhds 0) := by
  have hcore :=
    (tendsto_sixVertexCanonicalPerronLipschitz_div_width hc).const_mul
      (sixVertexFiniteRootDensityUniformBound c / lower * (2 * Real.pi))
  convert hcore using 1
  · funext k
    field_simp [hlower.ne']
  · norm_num

end
end StatMech.FrontierD
