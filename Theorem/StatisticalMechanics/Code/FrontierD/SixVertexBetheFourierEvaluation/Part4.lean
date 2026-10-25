/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier
    {c : Real} (hc : 2 < c) :
    SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔
      SixVertexSelectedBulkMatchesRootDensityFourier hc := by
  let lam := sixVertexAntiferroelectricLambda c
  have hFourier :
      Tendsto (sixVertexFreeEnergyFourierPartialSum lam) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) :=
    sixVertexFreeEnergyFourierPartialSum_tendsto
      (sixVertexAntiferroelectricLambda_pos hc)
  constructor
  · intro hbulk
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k)
      atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) at hbulk
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0)
    simpa [lam] using hbulk.sub hFourier
  · intro hmatch
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k -
        sixVertexFreeEnergyFourierPartialSum
          (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0) at hmatch
    change Tendsto (fun k =>
      sixVertexSelectedBulkLogKernel hc (Nat.log2 (k + 1)) k)
      atTop (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)))
    have hadd := hmatch.add hFourier
    convert hadd using 1
    · funext k
      dsimp [lam]
      ring
    · dsimp [lam]
      ring


end
end StatMech.FrontierD
