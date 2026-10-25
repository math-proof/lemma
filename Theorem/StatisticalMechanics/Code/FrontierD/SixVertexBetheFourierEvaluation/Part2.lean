/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum
    (lam : Real) (N : Nat) :
    sixVertexFreeEnergyFourierPartialSum lam N =
      lam / 2 + ∑ n ∈ range N, sixVertexFreeEnergySeriesTerm lam n := by
  unfold sixVertexFreeEnergyFourierPartialSum
  simp only [sixVertexFreeEnergyKernelFourierCoeff,
    sixVertexRootDensityFourierCoeff]
  rw [Finset.sum_congr rfl (fun n _ =>
    sixVertexFreeEnergyPairedFourierTerm_eq_seriesTerm lam n)]
  ring


theorem sixVertexFreeEnergyFourierPartialSum_tendsto
    {lam : Real} (hlam : 0 < lam) :
    Tendsto (sixVertexFreeEnergyFourierPartialSum lam) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) := by
  have hsum := (summable_sixVertexFreeEnergySeriesTerm hlam).hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : Nat => lam / 2) atTop (nhds (lam / 2)) :=
    tendsto_const_nhds
  have hadd := hconst.add hsum
  apply hadd.congr'
  filter_upwards [] with N
  exact (sixVertexFreeEnergyFourierPartialSum_eq_seriesPartialSum lam N).symm


end
end StatMech.FrontierD
