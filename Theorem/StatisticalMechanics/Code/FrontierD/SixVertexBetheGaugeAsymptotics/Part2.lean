/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheGaugeAsymptotics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheGaugeAsymptotics
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDensityGaugeOuterRadius_pos
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    0 < sixVertexDensityGaugeOuterRadius c rhoLower := by
  unfold sixVertexDensityGaugeOuterRadius
  exact div_pos
    (mul_pos hrho (div_pos
      (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc))) (by norm_num)

theorem sixVertexDensityGaugeInner_lt_outer
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    sixVertexDensityGaugeInnerRadius c rhoLower <
      sixVertexDensityGaugeOuterRadius c rhoLower := by
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have houter := sixVertexDensityGaugeOuterRadius_pos hc hrho
  unfold sixVertexDensityGaugeInnerRadius
  nlinarith [hrate.2]

theorem sixVertexDensityGaugeOuterRadius_le_half
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 ≤ rhoLower) :
    sixVertexDensityGaugeOuterRadius c rhoLower ≤
      rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2 := by
  let w := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hw : 0 < w := div_pos
    (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
    (sixVertexRootDensityScale_pos hc)
  unfold sixVertexDensityGaugeOuterRadius
  dsimp [w] at hw
  nlinarith


theorem eventually_sixVertexDensityGaugeNumericalMargins
    {c rhoLower : Real} (hc : 2 < c) (hrho : 0 < rhoLower) :
    ∀ᶠ N : Nat in atTop,
      sixVertexRootDensityContractionRate c *
          sixVertexDensityGaugeOuterRadius c rhoLower +
            sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤
        sixVertexDensityGaugeInnerRadius c rhoLower ∧
      sixVertexSymmetricScatteringBoundaryBound c +
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) <
        2 * Real.pi := by
  have hlower : 0 < rhoLower / 2 := by positivity
  have herr := tendsto_sixVertexFiniteDensityContinuumErrorOfLower c hlower
  have hjac := tendsto_sixVertexSymmetricJacobianTotalErrorOfLower c hlower
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have houter := sixVertexDensityGaugeOuterRadius_pos hc hrho
  have hgap : sixVertexRootDensityContractionRate c *
      sixVertexDensityGaugeOuterRadius c rhoLower <
        sixVertexDensityGaugeInnerRadius c rhoLower := by
    unfold sixVertexDensityGaugeInnerRadius
    nlinarith [hrate.2]
  have hboundary := sixVertexSymmetricScatteringBoundaryBound_lt_two_pi
    (c := c)
  have herrEventually : ∀ᶠ N : Nat in atTop,
      sixVertexRootDensityContractionRate c *
          sixVertexDensityGaugeOuterRadius c rhoLower +
            sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) <
        sixVertexDensityGaugeInnerRadius c rhoLower := by
    have hopen : Set.Iio
        (sixVertexDensityGaugeInnerRadius c rhoLower -
          sixVertexRootDensityContractionRate c *
            sixVertexDensityGaugeOuterRadius c rhoLower) ∈ nhds 0 :=
      Iio_mem_nhds (by linarith)
    filter_upwards [herr.eventually hopen] with N hN
    change sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) < _ at hN
    linarith
  have hjacEventually : ∀ᶠ N : Nat in atTop,
      sixVertexSymmetricScatteringBoundaryBound c +
          2 * sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) <
        2 * Real.pi := by
    have hopen : Set.Iio
        ((2 * Real.pi - sixVertexSymmetricScatteringBoundaryBound c) / 2) ∈
          nhds 0 := Iio_mem_nhds (by linarith)
    filter_upwards [hjac.eventually hopen] with N hN
    change sixVertexSymmetricJacobianTotalErrorOfLower c N (rhoLower / 2) < _ at hN
    linarith
  filter_upwards [herrEventually, hjacEventually] with N hE hJ
  exact ⟨hE.le, hJ⟩

end
end StatMech.FrontierD
