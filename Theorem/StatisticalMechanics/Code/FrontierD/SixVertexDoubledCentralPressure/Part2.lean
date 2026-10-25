/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDoubledCentralPressure
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCentralWidthRate_le_fullWidthRate
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexCentralWidthRate c k <= sixVertexFullWidthRate c k := by
  let N := sixVertexFourWidth 0 k
  let middle : Fin (N + 1) := ⟨N / 2, by omega⟩
  have hsector := sixVertexWidthSectorTopEigenvalue_le N c middle
  have hsectorPos : 0 < sixVertexWidthSectorTopEigenvalue N c middle := by
    exact sixVertexSectorTopEigenvalue_pos
      (sixVertexWidthSectorIndex_le N middle) hc
  have hlog := Real.log_le_log hsectorPos hsector
  have hdiv := div_le_div_of_nonneg_right hlog
    (by positivity : (0 : Real) <= N)
  simpa [sixVertexCentralWidthRate, sixVertexLambdaAlongFour,
    sixVertexLambda, sixVertexFullWidthRate, N, middle,
    sixVertexWidthSectorTopEigenvalue] using hdiv


theorem sixVertexFullWidthRate_le_log_two_div_add_doubledCentral
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFullWidthRate c k <=
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexCentralWidthRate c (2 * k + 1) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexLogWidthTop_le_log_two_add_half_doubledCentral
    N (sixVertexFourWidth_pos 0 k) (sixVertexFourWidth_even 0 k) hc
  have hdiv := div_le_div_of_nonneg_right h
    (by positivity : (0 : Real) <= N)
  have hdouble : sixVertexFourWidth 0 (2 * k + 1) = N + N := by
    dsimp [N, sixVertexFourWidth]
    omega
  unfold sixVertexFullWidthRate sixVertexCentralWidthRate
  rw [sixVertexLambdaAlongFour, sixVertexLambda, hdouble]
  dsimp [N] at hdiv ⊢
  convert hdiv using 1 <;>
    push_cast <;>
    field_simp [Nat.cast_ne_zero.mpr (sixVertexFourWidth_pos 0 k).ne'] <;>
    ring


theorem tendsto_sixVertexFullWidthRate_canonicalPerron
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexFullWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  let a := sixVertexAntiferroelectricFreeEnergyValue
    (sixVertexAntiferroelectricLambda c)
  have hcentral : Tendsto (sixVertexCentralWidthRate c) atTop (nhds a) :=
    tendsto_sixVertexCentralWidthRate_canonicalPerron hc
  have hindex : Tendsto (fun k : Nat => 2 * k + 1) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [eventually_ge_atTop K] with k hk
    omega
  have hcentralDouble : Tendsto (fun k =>
      sixVertexCentralWidthRate c (2 * k + 1)) atTop (nhds a) := by
    simpa only [Function.comp_apply] using hcentral.comp hindex
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    refine tendsto_atTop.2 (fun K => ?_)
    filter_upwards [eventually_ge_atTop K] with k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  have hboundary : Tendsto (fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) :=
    hwidthReal.const_div_atTop (Real.log 2)
  have hupper : Tendsto (fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexCentralWidthRate c (2 * k + 1)) atTop (nhds a) := by
    simpa only [zero_add] using hboundary.add hcentralDouble
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcentral hupper
  · exact Filter.Eventually.of_forall
      (sixVertexCentralWidthRate_le_fullWidthRate (by linarith))
  · exact Filter.Eventually.of_forall
      (sixVertexFullWidthRate_le_log_two_div_add_doubledCentral
        (by linarith))


theorem sixVertexFullAreaDensity_tendsto_widthRate
    {c : Real} (hc : 0 < c) (k : Nat) :
    Tendsto (sixVertexFullAreaDensity c k) atTop
      (nhds (sixVertexFullWidthRate c k)) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexFixedWidth_log_partition_div_height_tendsto N hc
  have hdiv := h.div_const (N : Real)
  have hdiv' : Tendsto (fun M : Nat =>
      Real.log (sixVertexFixedWidthPartitionSum N M c) / (M : Real) /
        (N : Real)) atTop (nhds (sixVertexFullWidthRate c k)) := by
    simpa [sixVertexFullWidthRate, N] using hdiv
  apply hdiv'.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with M hM
  unfold sixVertexFullAreaDensity
  dsimp [N]
  field_simp


theorem sixVertexFull_iteratedLimit_of_canonicalPerron
    {c : Real} (hc : 2 < c) :
    SixVertexHasIteratedLimit (sixVertexFullAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) :=
  ⟨sixVertexFullWidthRate c,
    sixVertexFullAreaDensity_tendsto_widthRate (by linarith),
    tendsto_sixVertexFullWidthRate_canonicalPerron hc⟩


theorem fkQgt4_sixVertexFull_iteratedLimit
    {q : Real} (hq : 4 < q) :
    SixVertexHasIteratedLimit
      (sixVertexFullAreaDensity (fkQgt4SixVertexWeight q))
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q))) :=
  sixVertexFull_iteratedLimit_of_canonicalPerron
    (two_lt_fkQgt4SixVertexWeight hq)

end
end StatMech.FrontierD
