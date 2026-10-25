/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) :
    Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : Real) * sixVertexAntiferroelectricGapRate
          (sixVertexAntiferroelectricLambda c))) ↔
      SixVertexFixedChargeMatchesOffsetFourier c r := by
  let lam := sixVertexAntiferroelectricLambda c
  let gap := sixVertexAntiferroelectricGapRate lam
  have hOffset :
      Tendsto (fun k => (r : Real) * sixVertexOffsetFourierPartialSum lam k)
        atTop (nhds ((r : Real) * gap)) :=
    (sixVertexOffsetFourierPartialSum_tendsto
      (sixVertexAntiferroelectricLambda_pos hc)).const_mul (r : Real)
  constructor
  · intro hratio
    have hadd := hratio.add hOffset
    change Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0)
    simpa [lam, gap] using hadd
  · intro hmatch
    change Tendsto (fun k => sixVertexFixedChargeLogRatio c r k +
      (r : Real) * sixVertexOffsetFourierPartialSum
        (sixVertexAntiferroelectricLambda c) k) atTop (nhds 0) at hmatch
    have hsub := hmatch.sub hOffset
    convert hsub using 1
    · funext k
      dsimp [lam]
      ring
    · dsimp [gap, lam]
      ring


theorem sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier
    {c : Real} (hc : 2 < c) (r : Nat) :
    Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : Real) *
          sixVertexAntiferroelectricGapRate
            (sixVertexAntiferroelectricLambda c)))) ↔
      SixVertexFixedChargeMatchesOffsetFourier c r :=
  (sixVertexFixedChargeRatio_tendsto_iff_logRatio (by linarith) r).trans
    (sixVertexFixedChargeLogRatio_tendsto_iff_matchesOffsetFourier hc r)


theorem sixVertexAntiferroelectricTransferConclusion_of_rootDensityFourier
    {c : Real} (hc : 2 < c)
    (hphase : SixVertexSelectedHalfFilledWaveHasPositivePhase c)
    (hbulk : SixVertexSelectedBulkMatchesRootDensityFourier hc)
    (hoffset : ∀ r : Nat, 1 ≤ r →
      SixVertexFixedChargeMatchesOffsetFourier c r) :
    SixVertexAntiferroelectricTransferConclusion c
      (sixVertexAntiferroelectricLambda c) := by
  refine ⟨?_, ?_⟩
  · exact sixVertexBalanced_iteratedLimit_of_positivePhase_of_bulkFreeEnergy
      hc hphase
      ((sixVertexSelectedBulkFreeEnergyAsymptotic_iff_matchesRootDensityFourier
        hc).2 hbulk)
  · intro r hr
    exact (sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier hc r).2
      (hoffset r hr)

end
end StatMech.FrontierD
