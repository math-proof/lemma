/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part4
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexBalancedAreaDensity_tendsto_widthRate
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (sixVertexBalancedAreaDensity c k) atTop
      (nhds (sixVertexCentralWidthRate c k)) := by
  let N := sixVertexFourWidth 0 k
  have h := sixVertexLambda_log_trace_div_height_tendsto
    N 0 (sixVertexFourWidth_even 0 k) (Nat.zero_le _) hc
  have hdiv := h.div_const (N : ℝ)
  have hdiv' : Tendsto (fun M : ℕ =>
      Real.log (Matrix.trace (sixVertexSectorTransfer N (N / 2 - 0) c ^ M)) /
        (M : ℝ) / (N : ℝ)) atTop
      (nhds (sixVertexCentralWidthRate c k)) := by
    simpa [sixVertexCentralWidthRate, sixVertexLambdaAlongFour, N] using hdiv
  apply hdiv'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  unfold sixVertexBalancedAreaDensity sixVertexBalancedSectorPartitionSum
  dsimp [N]
  field_simp


end StatMech.FrontierD
