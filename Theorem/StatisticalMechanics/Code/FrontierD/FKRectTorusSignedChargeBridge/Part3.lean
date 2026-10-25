/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge.Part3
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Fin (R.medialTorus.width + 1)) (lam : Real) :
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectSignedChargeTilt R q lam n omega) =
      Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
              R.medialTorus.height) /
        fkRectCriticalReducedZ R q := by
  let fiber : R.Configuration -> Real := fun omega =>
    ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectSignedChargeTilt R q lam n omega) =
        ∑ omega : R.Configuration,
          fiber omega / fkRectCriticalReducedZ R q := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [fkRectCriticalRandomClusterProb, fkRectSignedChargeTilt]
      dsimp only [fiber]
      have hw := (fkRectCriticalReducedWeight_pos R hq omega).ne'
      have hz := (fkRectCriticalReducedZ_pos R hq).ne'
      field_simp
    _ = (∑ omega : R.Configuration, fiber omega) /
          fkRectCriticalReducedZ R q := by
      rw [Finset.sum_div]
    _ = fkRectOrientedLoopSectorPartitionSum R n lam /
          fkRectCriticalReducedZ R q := by
      rfl
    _ = Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^
              R.medialTorus.height) /
          fkRectCriticalReducedZ R q := by
      rw [fkRectOrientedLoopSectorPartitionSum_eq_sectorTrace]


theorem sum_rcProb_mul_fkRectSignedChargeTilt_eq_canonicalSectorTrace_div_Z
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (n : Fin (R.medialTorus.width + 1)) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    (∑ omega : R.Configuration,
      fkRectCriticalRandomClusterProb R q omega *
        fkRectSignedChargeTilt R q lam n omega) =
      Matrix.trace
          (sixVertexSectorTransfer R.medialTorus.width n.val
            (fkQgt4SixVertexWeight q) ^ R.medialTorus.height) /
        fkRectCriticalReducedZ R q := by
  dsimp only
  rw [sum_rcProb_mul_fkRectSignedChargeTilt_eq_sectorTrace_div_Z
    R (by linarith) n]
  rw [exp_half_add_exp_neg_half_sixVertexLambda_fkQgt4 hq]

end
end StatMech.FrontierD
