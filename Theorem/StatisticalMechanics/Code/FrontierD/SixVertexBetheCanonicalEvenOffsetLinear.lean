/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalEvenOffsetLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLinearBound


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem halfDensityInvWidthConstant_nonneg
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) :
    0 <= sixVertexHalfDensityInvWidthConstantOfLower c lower := by
  unfold sixVertexHalfDensityInvWidthConstantOfLower
  apply div_nonneg
  · unfold sixVertexFiniteDensityContinuumErrorOfLower
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
    have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      positivity
    positivity
  · exact sub_nonneg.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

theorem fixedDensityInvWidthConstant_nonneg
    {c lower : Real} (hc : 2 < c) (hlower : 0 < lower) (r : Nat) :
    0 <= sixVertexFixedChargeDensityInvWidthConstantOfLower c r lower := by
  unfold sixVertexFixedChargeDensityInvWidthConstantOfLower
  apply div_nonneg
  · unfold sixVertexFixedChargeDensityStabilityErrorOfLower
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    have hscale := sixVertexRootDensityScale_pos hc
    have hL := sixVertexRootDensityKernelLipschitzBound_pos hc
    have hK := sixVertexRootDensityKernelUniformBound_nonneg hc
    have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
    have hU : 0 < sixVertexFiniteRootDensityUniformBound c := by
      unfold sixVertexFiniteRootDensityUniformBound
      positivity
    apply add_nonneg
    · exact add_nonneg (mul_nonneg hrate.1 (by positivity))
        (mul_nonneg (by positivity) hK)
    · unfold sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
      exact div_nonneg (add_nonneg (by positivity)
        (mul_nonneg (by positivity) hK)) (by positivity)
  · exact sub_nonneg.mpr (sixVertexRootDensityContractionRate_mem_Ico hc).2.le

end
end StatMech.FrontierD
