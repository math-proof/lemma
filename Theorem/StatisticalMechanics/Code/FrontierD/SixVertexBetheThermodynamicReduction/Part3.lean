/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexFixedChargeRatio_pos {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    0 < sixVertexFixedChargeRatio c r k := by
  apply div_pos (sixVertexLambdaAlongFour_pos hc r k)
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k)
    (Nat.zero_le _) hc).1


theorem sixVertexFixedChargeLogRatio_eq {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    sixVertexFixedChargeLogRatio c r k =
      Real.log (sixVertexLambdaAlongFour c r k) -
        Real.log (sixVertexLambda (sixVertexFourWidth r k) 0
          (sixVertexFourWidth_even r k) (Nat.zero_le _) c) := by
  rw [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio, Real.log_div]
  · exact (sixVertexLambdaAlongFour_pos hc r k).ne'
  · exact ((sixVertexLambda_isPerronFrobenius
      (sixVertexFourWidth r k) 0 (sixVertexFourWidth_even r k)
      (Nat.zero_le _) hc).1).ne'


theorem sixVertexFixedChargeTraceLogRatio_div_height_tendsto
    {c : Real} (hc : 0 < c) (r k : Nat) :
    Tendsto (fun M : Nat =>
      Real.log
          (Matrix.trace
                (sixVertexSectorTransfer (sixVertexFourWidth r k)
                  (sixVertexFourWidth r k / 2 - r) c ^ M) /
            Matrix.trace
                (sixVertexSectorTransfer (sixVertexFourWidth r k)
                  (sixVertexFourWidth r k / 2) c ^ M)) /
        (M : Real))
      atTop
      (nhds (sixVertexFixedChargeLogRatio c r k)) := by
  have h := sixVertexLambda_log_trace_ratio_div_height_tendsto
    (sixVertexFourWidth r k) r (sixVertexFourWidth_even r k)
      (sixVertexFourWidth_charge_le r k) hc
  simpa only [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio,
    sixVertexLambdaAlongFour] using h


theorem sixVertexFixedChargeRatio_tendsto_iff_logRatio
    {c L : ℝ} (hc : 0 < c) (r : ℕ) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop (nhds (Real.exp L)) ↔
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop (nhds L) := by
  constructor
  · intro h
    have hlog := (Real.continuousAt_log (Real.exp_ne_zero L)).tendsto.comp h
    simpa [sixVertexFixedChargeLogRatio] using hlog
  · intro h
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp h
    apply hexp.congr'
    filter_upwards [] with k
    exact Real.exp_log (sixVertexFixedChargeRatio_pos hc r k)


theorem sixVertexAntiferroelectricGapFormula_iff_logBethe
    {c lam : ℝ} (hc : 0 < c) (r : ℕ) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : ℝ) *
          sixVertexAntiferroelectricGapRate lam))) ↔
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam)) := by
  exact sixVertexFixedChargeRatio_tendsto_iff_logRatio hc r


end StatMech.FrontierD
