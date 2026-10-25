/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourierRootDensityNormBound_nonneg
    (lam : Real) :
    0 <= sixVertexFourierRootDensityNormBound lam := by
  unfold sixVertexFourierRootDensityNormBound
  have hsum : 0 <= ∑' n : Nat, sixVertexFourierRootDensityMajorant lam n :=
    tsum_nonneg fun n => by
      unfold sixVertexFourierRootDensityMajorant
      positivity
  linarith

theorem norm_sixVertexFourierRootDensity_le
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    ‖sixVertexFourierRootDensity lam alpha‖ <=
      sixVertexFourierRootDensityNormBound lam := by
  have hmajor := summable_sixVertexFourierRootDensityMajorant hlam
  have hnorm : Summable (fun n : Nat =>
      ‖sixVertexFourierRootDensityTerm lam n alpha‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha) hmajor
  rw [sixVertexFourierRootDensity, sixVertexFourierRootDensityNormBound]
  calc
    ‖1 / 2 + ∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha‖
      <= ‖(1 / 2 : Real)‖ +
          ‖∑' n : Nat, sixVertexFourierRootDensityTerm lam n alpha‖ :=
        norm_add_le _ _
    _ <= 1 / 2 + ∑' n : Nat,
        ‖sixVertexFourierRootDensityTerm lam n alpha‖ := by
      rw [Real.norm_of_nonneg (by norm_num : (0 : Real) <= 1 / 2)]
      gcongr
      exact norm_tsum_le_tsum_norm hnorm
    _ <= 1 / 2 + ∑' n : Nat,
        sixVertexFourierRootDensityMajorant lam n := by
      have h := hnorm.tsum_le_tsum
        (fun n => norm_sixVertexFourierRootDensityTerm_le hlam n alpha) hmajor
      linarith


end
end StatMech.FrontierD
