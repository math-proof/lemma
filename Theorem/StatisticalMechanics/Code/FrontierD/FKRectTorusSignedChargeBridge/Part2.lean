/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge.Part2
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOrientedLoopSectorPartitionSum_eq_generic
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) :
    fkRectOrientedLoopSectorPartitionSum R n lam =
      fkOrientedLoopSectorPartitionSum R.medialTorus n lam := by
  unfold fkRectOrientedLoopSectorPartitionSum
    fkOrientedLoopSectorPartitionSum fkRectOrientedLoopWeight
  rw [Equiv.sum_comp (fkRectConfigurationToMedialPairing R)
    (fun pairing => ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkOrientedLoopPairingWeight lam pairing arrows
      else 0)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro arrows harrows
  by_cases hn : sixVertexUpCount
      (svTorusVerticalRows R.medialTorus arrows
        (svFinLast R.medialTorus.height_pos)) = n.val
  · simp [hn]
  · simp [hn]

theorem fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) :
    fkRectOrientedLoopSectorPartitionSum R n lam =
      Matrix.trace
        (sixVertexSectorTransfer R.medialTorus.width n.val
          (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
            R.medialTorus.height) := by
  rw [fkRectOrientedLoopSectorPartitionSum_eq_generic,
    fkOrientedLoopSectorPartitionSum_eq_sixVertexSector]
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace _ _ _


theorem exp_add_exp_neg_sixVertexLambda_fkQgt4
    {q : Real} (hq : 4 < q) :
    Real.exp
        (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) +
      Real.exp
        (-sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) =
      Real.sqrt q := by
  have hc := cosh_sixVertexAntiferroelectricLambda_fkQgt4 hq
  rw [Real.cosh_eq] at hc
  linarith


theorem exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4
    {q : Real} (hq : 4 < q) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    Real.exp (lam / 2) + Real.exp (-lam / 2) =
      fkQgt4SixVertexWeight q := by
  dsimp only
  let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
  have hsum : Real.exp lam + Real.exp (-lam) = Real.sqrt q := by
    exact exp_add_exp_neg_sixVertexLambda_fkQgt4 hq
  have hprod : Real.exp (lam / 2) * Real.exp (-lam / 2) = 1 := by
    rw [<- Real.exp_add]
    rw [<- Real.exp_zero]
    congr 1
    ring
  have hpos : 0 < Real.exp (lam / 2) + Real.exp (-lam / 2) := by positivity
  have ha2 : Real.exp (lam / 2) ^ 2 = Real.exp lam := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hb2 : Real.exp (-lam / 2) ^ 2 = Real.exp (-lam) := by
    rw [pow_two, <- Real.exp_add]
    congr 1
    ring
  have hsquare :
      (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ 2 =
        2 + Real.sqrt q := by
    nlinarith
  have hcSquare := fkQgt4SixVertexWeight_sq hq
  have hcNonneg : 0 <= fkQgt4SixVertexWeight q := by
    unfold fkQgt4SixVertexWeight
    positivity
  dsimp only [lam] at hpos hsquare
  nlinarith


end
end StatMech.FrontierD
