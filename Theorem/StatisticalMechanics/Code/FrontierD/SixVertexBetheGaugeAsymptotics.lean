/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFiniteDensityContinuumErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexFiniteDensityContinuumErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexFiniteDensityContinuumErrorOfLower]
  field_simp [hN0, hlower.ne', Real.pi_ne_zero]

theorem tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianDiagonalErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := 4 * Real.pi *
      (sixVertexFiniteRootDensityLipschitzConstant c : Real) / lower ^ 2 +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexSymmetricJacobianDiagonalErrorOfLower]
  field_simp [hN0, hlower.ne']

theorem tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianOffDiagonalErrorOfLower c N lower)
      atTop (nhds 0) := by
  let A := ((2 * Real.pi) *
      (sixVertexSymmetricScatteringLipschitzConstant c : Real) +
    2 * (sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1))) / lower
  have h := tendsto_const_div_atTop_nhds_zero_nat A
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp [A, sixVertexSymmetricJacobianOffDiagonalErrorOfLower]
  field_simp [hN0, hlower.ne']

theorem tendsto_sixVertexSymmetricJacobianTotalErrorOfLower
    (c : Real) {lower : Real} (hlower : 0 < lower) :
    Tendsto (fun N : Nat =>
      sixVertexSymmetricJacobianTotalErrorOfLower c N lower)
      atTop (nhds 0) := by
  simpa only [sixVertexSymmetricJacobianTotalErrorOfLower, zero_add] using
    (tendsto_sixVertexSymmetricJacobianDiagonalErrorOfLower c hlower).add
      (tendsto_sixVertexSymmetricJacobianOffDiagonalErrorOfLower c hlower)


end
end StatMech.FrontierD
