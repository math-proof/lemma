/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOffsetRapidityLipschitzBound_pos
    {lam : Real} (hlam : 0 < lam) :
    0 < sixVertexOffsetRapidityLipschitzBound lam := by
  unfold sixVertexOffsetRapidityLipschitzBound
  have hsum : 0 <= ∑' n : Nat,
      sixVertexOffsetCorrectionLipschitzTerm lam n :=
    tsum_nonneg (sixVertexOffsetCorrectionLipschitzTerm_nonneg lam)
  positivity

theorem lipschitzWith_sixVertexOffsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    LipschitzWith (sixVertexOffsetRapidityLipschitzNNReal lam)
      (sixVertexOffsetRapidityProfile lam) := by
  have hL : 0 <= sixVertexOffsetRapidityLipschitzBound lam :=
    (sixVertexOffsetRapidityLipschitzBound_pos hlam).le
  have hLcoe : (sixVertexOffsetRapidityLipschitzNNReal lam : Real) =
      sixVertexOffsetRapidityLipschitzBound lam := by
    exact Real.coe_toNNReal _ hL
  apply LipschitzWith.of_dist_le_mul
  intro alpha beta
  rw [Real.dist_eq, Real.dist_eq, hLcoe]
  have hAlpha := summable_sixVertexOffsetCorrectionTerm hlam alpha
  have hBeta := summable_sixVertexOffsetCorrectionTerm hlam beta
  have hDiff := hAlpha.sub hBeta
  have hMajor := summable_sixVertexOffsetCorrectionLipschitzTerm hlam
  have hMajorScaled := hMajor.mul_right |alpha - beta|
  have hcorr :
      |(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta| <=
        (∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n) *
          |alpha - beta| := by
    rw [<- hAlpha.tsum_sub hBeta, <- tsum_mul_right]
    calc
      |∑' n : Nat, (sixVertexOffsetCorrectionTerm lam n alpha -
          sixVertexOffsetCorrectionTerm lam n beta)| =
        ‖∑' n : Nat, (sixVertexOffsetCorrectionTerm lam n alpha -
          sixVertexOffsetCorrectionTerm lam n beta)‖ := by
            rw [Real.norm_eq_abs]
      _ <= ∑' n : Nat,
          ‖sixVertexOffsetCorrectionTerm lam n alpha -
            sixVertexOffsetCorrectionTerm lam n beta‖ :=
        norm_tsum_le_tsum_norm hDiff.norm
      _ <= ∑' n : Nat,
          sixVertexOffsetCorrectionLipschitzTerm lam n *
            |alpha - beta| := by
        apply hDiff.norm.tsum_le_tsum
        · intro n
          rw [Real.norm_eq_abs]
          exact abs_sixVertexOffsetCorrectionTerm_sub_le lam n alpha beta
        · exact hMajorScaled
  unfold sixVertexOffsetRapidityProfile
  have hlinear :
      |-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)| =
        (1 / (2 * Real.pi)) * |alpha - beta| := by
    have hneg : (-1 / (2 * Real.pi) : Real) <= 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    rw [show -alpha / (2 * Real.pi) - -beta / (2 * Real.pi) =
      (-1 / (2 * Real.pi)) * (alpha - beta) by ring,
      abs_mul, abs_of_nonpos hneg]
    ring
  calc
    |(-alpha / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
        (-beta / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta)| <=
      |-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)| +
        |(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta| := by
      rw [show (-alpha / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
        (-beta / (2 * Real.pi) +
          ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta) =
        (-alpha / (2 * Real.pi) - -beta / (2 * Real.pi)) +
          ((∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) -
            ∑' n : Nat, sixVertexOffsetCorrectionTerm lam n beta) by ring]
      exact abs_add_le _ _
    _ <= (1 / (2 * Real.pi)) * |alpha - beta| +
        (∑' n : Nat, sixVertexOffsetCorrectionLipschitzTerm lam n) *
          |alpha - beta| := add_le_add hlinear.le hcorr
    _ = sixVertexOffsetRapidityLipschitzBound lam * |alpha - beta| := by
      unfold sixVertexOffsetRapidityLipschitzBound
      ring

end
end StatMech.FrontierD
