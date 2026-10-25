/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_exists_sixVertexHalfFilledPerronGaugeWitness
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k epsilon p := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoBase, hrhoBase, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  let rhoLower := min rhoBase epsilon
  have hrhoLower : 0 < rhoLower := lt_min hrhoBase hepsilon
  have hrhoLowerBase : rhoLower ≤ rhoBase := min_le_left _ _
  have hrhoLowerEpsilon : rhoLower ≤ epsilon := min_le_right _ _
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
  have hfloorLe :
      (sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c ≤ 1 := by
    rw [div_le_one (sixVertexRootDensityScale_pos hc)]
    exact (sixVertexRootDensityScale_bounds hc).1
  have houterEpsilon : outer < epsilon := by
    have hout := houter c hac.le
    have hproduct : rhoLower *
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c) ≤ epsilon := by
      calc
        rhoLower * ((sixVertexAnisotropyMagnitude c - 1) /
            sixVertexRootDensityScale c) ≤ rhoLower * 1 := by
          gcongr
        _ ≤ epsilon := by simpa using hrhoLowerEpsilon
    nlinarith
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFiniteDensityContinuumErrorOfLower t
            (sixVertexFourWidth 0 k) (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth 0 k) (rhoLower / 2) < 2 * Real.pi :=
    hwidth.eventually hmargins
  filter_upwards [hmarginsK] with k hkMargins
  have hbaseGauge := eventually_sixVertexHalfFilledContinuationGauge_lt
    ha houterPos k
  have hcand :=
    eventually_sixVertexHalfFilledBetheCandidate_eq_top_and_wave_ne_zero k
  obtain ⟨c₀, hc₀Gauge, hc₀Cand, hc₀large⟩ :=
    (hbaseGauge.and (hcand.and (eventually_ge_atTop (c + 1)))).exists
  let b := c₀ + 1
  have hc₀a : a < c₀ := by linarith
  have hc₀Ioo : c₀ ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hc₀a, by linarith⟩
  have hc₀Icc : c₀ ∈ Set.Icc a b := ⟨hc₀Ioo.1.le, hc₀Ioo.2.le⟩
  have hcIoo : c ∈ Set.Ioo a b := by
    dsimp [b]
    exact ⟨hac, by linarith⟩
  have hcIcc : c ∈ Set.Icc a b := ⟨hcIoo.1.le, hcIoo.2.le⟩
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexHalfFilledBetheContinuationPoint ha hc₀Icc k) < outer :=
    hc₀Gauge b hc₀Icc
  obtain ⟨roots, _hrootsBase, hrootsData, _hrootsAnalytic, hperron,
      hrootsGauge⟩ :=
    exists_sixVertexHalfFilledPerronSheet_of_densityGauge
      ha (by dsimp [b]; linarith) hc₀Ioo k
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        exact hrhoLowerBase.trans (by
          simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
            sixVertexFourierPhysicalDensityFamily_apply] using
              hrho t.1 t.2.1 x))
      hio (fun t => houter t.1 t.2.1)
      (fun t => (hkMargins t.1 t.2.1).1)
      (fun t => (hkMargins t.1 t.2.1).2)
      hz₀g (hc₀Cand (ha.trans hc₀Ioo.1)).1
      (hc₀Cand (ha.trans hc₀Ioo.1)).2
  obtain ⟨z, hzg, hzparam, hzroots⟩ := hrootsGauge c hcIcc
  have hdirect : sixVertexWeightedFiniteDensityGauge hc
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (roots c)
      (sixVertexFourierPhysicalDensityMap hc) ≤ inner := by
    have hzg' : sixVertexWeightedFiniteDensityGauge
        (ha.trans_le z.2.1.1)
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) z.1.2
        (sixVertexFourierPhysicalDensityMap (ha.trans_le z.2.1.1)) ≤ inner := by
      simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      sixVertexFourierPhysicalDensityFamily_apply,
      sixVertexFourierPhysicalDensityMap] using hzg
    rw [sixVertexWeightedFiniteDensityGauge_fourier_congr
      (ha.trans_le z.2.1.1) hc hzparam hzroots] at hzg'
    exact hzg'
  refine ⟨roots c, ?_, hdirect.trans_lt (hio.trans houterEpsilon)⟩
  exact ⟨(hrootsData c hcIcc).1, (hrootsData c hcIcc).2, hperron hcIoo⟩


end
end StatMech.FrontierD
