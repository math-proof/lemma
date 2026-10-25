/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Stirling
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution
    {c : Real} (hc : 2 < c) :
    SixVertexSelectedBulkFreeEnergyAsymptotic hc ↔
      Tendsto (fun k => sixVertexSelectedBulkLogContribution hc
        (Nat.log2 (k + 1)) k) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c))) := by
  apply tendsto_congr'
  filter_upwards [] with k
  exact (sixVertexSelectedBulkLogContribution_eq_logKernel hc _ _).symm


theorem sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
        (nhds (sixVertexAntiferroelectricFreeEnergyValue
          (sixVertexAntiferroelectricLambda c))) ↔
      SixVertexSelectedBulkFreeEnergyAsymptotic hc := by
  have hident :=
    sixVertexHasSymmetricBetheIdentification_of_selectedWaveHasPositivePhase
      hc hphase
  refine (sixVertexCentralWidthRate_tendsto_iff_symmetricBetheRootAverage
      hc (sixVertexPositiveHalfBetheRootFamily hc) hident).trans ?_
  exact (sixVertexSelectedRootAverage_tendsto_iff_bulkLog2 hc).trans
    (sixVertexSelectedBulkFreeEnergyAsymptotic_iff_normContribution hc).symm


theorem sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
    (hbulk : SixVertexSelectedBulkFreeEnergyAsymptotic hc) :
    SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue
        (sixVertexAntiferroelectricLambda c)) := by
  apply (sixVertexBalanced_iteratedLimit_iff_widthRate (by linarith)).2
  exact (sixVertexCentralWidthRate_tendsto_iff_bulkFreeEnergy_of_positivePhase
    hc hphase).2 hbulk

end
end StatMech.FrontierD
