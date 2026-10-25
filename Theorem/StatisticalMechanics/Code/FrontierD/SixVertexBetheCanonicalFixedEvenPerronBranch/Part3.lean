/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p ∧
        ∀ x, lower ≤ sixVertexFiniteRootDensity c
          (sixVertexFourWidth (2 * s) k)
          ((s + k + 1) + (s + k + 1)) p x := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  refine ⟨rhoLower / 2, by positivity, ?_⟩
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexFixedChargeDensityGaugeNumericalMargins_Ici
      ha hrhoLower (2 * s)
  have hwidth : Tendsto (sixVertexFourWidth (2 * s)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hmarginsK : ∀ᶠ k : Nat in atTop, ∀ t, a ≤ t →
      sixVertexRootDensityContractionRate t * outer +
          sixVertexFixedChargeDensityStabilityErrorOfLower t
            (sixVertexFourWidth (2 * s) k) (2 * s) (rhoLower / 2) ≤ inner ∧
        sixVertexSymmetricScatteringBoundaryBound t +
            2 * sixVertexSymmetricJacobianTotalErrorOfLower t
              (sixVertexFourWidth (2 * s) k) (rhoLower / 2) < 2 * Real.pi :=
    hwidth.eventually hmargins
  have hchargeRatio : Tendsto (fun k : Nat =>
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp hwidth)
  have hchargeSmall : ∀ᶠ k : Nat in atTop,
      ((2 * s : Nat) : Real) / sixVertexFourWidth (2 * s) k <
        outer * (2 * Real.pi) :=
    hchargeRatio.eventually (Iio_mem_nhds (mul_pos houterPos (by positivity)))
  filter_upwards [hmarginsK, hchargeSmall] with k hkMargins hkCharge
  have hbaseGauge := eventually_sixVertexFixedChargeContinuationGauge_lt
    ha (2 * s) k hkCharge
  have hbasePerron :=
    eventually_sixVertexFixedEvenChargeBetheCandidate_eq_top s k
  have hbaseWave :=
    eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero (2 * s) k
  obtain ⟨c₀, hc₀Gauge, hc₀Perron, hc₀Wave, hc₀large⟩ :=
    (hbaseGauge.and
      (hbasePerron.and (hbaseWave.and (eventually_ge_atTop (c + 1))))).exists
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
  let m := s + k + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hcharge : sixVertexFourWidth (2 * s) k =
      2 * (m + m) + 2 * (2 * s) := by
    dsimp [m]
    unfold sixVertexFourWidth
    omega
  let z₀ := sixVertexCanonicalFixedEvenChargeContinuationPoint
    ha hc₀Icc s k
  have hz₀g : sixVertexContinuationWeightedFiniteDensityGauge ha
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFourierPhysicalDensityFamily ha) z₀ < outer := by
    change sixVertexWeightedFiniteDensityGauge (ha.trans_le hc₀Icc.1)
      (sixVertexFourWidth (2 * s) k) (m + m)
      (sixVertexFixedEvenChargeBetheRoots (ha.trans_le hc₀Icc.1) s k)
      (sixVertexContinuumDensityAt (sixVertexFourierPhysicalDensityFamily ha)
        ⟨c₀, hc₀Icc⟩) < outer
    rw [sixVertexWeightedFiniteDensityGauge_fixedEvenCharge_canonical]
    exact hc₀Gauge b hc₀Icc
  obtain ⟨roots, hroots₀, hrootsData, hrootsAnalytic, hrootsGauge⟩ :=
    exists_sixVertexAnalyticEvenSymmetricBetheBranch_of_fixedChargeDensityGauge
      ha (by dsimp [b]; linarith) hc₀Icc hm
      (sixVertexFourWidth_pos (2 * s) k) hcharge
      (sixVertexFourierPhysicalDensityFamily ha)
      (sixVertexFourierPhysicalDensityFamily_continuumEquation ha)
      (intervalIntegral_sixVertexFourierPhysicalDensityFamily ha)
      hrhoLower (fun t x => by
        simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
          sixVertexFourierPhysicalDensityFamily_apply] using
            hrho t.1 t.2.1 x)
      hio (fun t => houter t.1 t.2.1)
      (fun t => (hkMargins t.1 t.2.1).1)
      (fun t => (hkMargins t.1 t.2.1).2)
      z₀ hz₀g
      (sixVertexCanonicalFixedEvenChargeContinuationPoint_projection
        ha hc₀Icc s k)
  have hperron := sixVertexAnalyticEvenSymmetricBetheCandidate_eqOn_top
    (N := sixVertexFourWidth (2 * s) k) (m := m) hm
    (by dsimp [m]; unfold sixVertexFourWidth; omega)
    isPreconnected_Ioo isOpen_Ioo
    (fun t ht => by change 2 < t; linarith [ht.1]) roots
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).1)
    (fun t ht => (hrootsData t ⟨ht.1.le, ht.2.le⟩).2)
    hrootsAnalytic hc₀Ioo
    (by
      rw [hroots₀]
      apply sixVertexCoordinateBetheWave_finCast_ne_zero
        (sixVertexFixedEvenChargeBetheParticleCount_eq s k)
      exact hc₀Wave (ha.trans hc₀Ioo.1))
    (by
      rw [hroots₀]
      have hvalue := sixVertexSectorTopEigenvalue_eq_of_finCast
        (sixVertexFixedEvenChargeBetheParticleCount_eq s k)
        (by
          have h := sixVertexFixedChargeBetheParticleCount_twice_le (2 * s) k
          omega)
        (by unfold sixVertexFourWidth; omega)
        c₀ (sixVertexFixedEvenChargeBetheEigenvalueValue
          (ha.trans hc₀Ioo.1) s k)
        (hc₀Perron (ha.trans hc₀Ioo.1))
      have hpositive (j : Fin m) :
          sixVertexFixedEvenPositiveBetheRoots
              (ha.trans hc₀Ioo.1) s k j ∈ Set.Ioo 0 Real.pi := by
        have hopen := sixVertexFixedEvenChargeRoots_mem_open_canonical
          (ha.trans hc₀Ioo.1) s k
        have hpos := sixVertexEvenSymmetricLift_positive_mem_Ioo
          (q := sixVertexEvenPositiveHalfProjection m
            (sixVertexFixedEvenChargeBetheRoots
              (ha.trans hc₀Ioo.1) s k))
          (by
            rw [sixVertexEvenSymmetricLift_projection m hopen.2.1]
            exact hopen) j
        exact hpos
      change sixVertexSymmetricBetheEigenvalueKernel c₀
          (sixVertexFixedEvenPositiveBetheRoots
            (ha.trans hc₀Ioo.1) s k) = _
      rw [sixVertexSymmetricBetheEigenvalueKernel_eq_value c₀ _ hpositive]
      exact hvalue)
  obtain ⟨z, hzg, hzparam, hzroots⟩ := hrootsGauge c hcIcc
  have hzg' : sixVertexWeightedFiniteDensityGauge
      (ha.trans_le z.2.1.1) (sixVertexFourWidth (2 * s) k) (m + m)
      z.1.2 (sixVertexFourierPhysicalDensityMap
        (ha.trans_le z.2.1.1)) ≤ inner := by
    simpa only [sixVertexContinuationWeightedFiniteDensityGauge,
      sixVertexContinuumDensitySection, sixVertexContinuumDensityAt,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      sixVertexFourierPhysicalDensityFamily_apply,
      sixVertexFourierPhysicalDensityMap] using hzg
  rw [sixVertexWeightedFiniteDensityGauge_fourier_congr_fixedCharge
    (ha.trans_le z.2.1.1) hc hzparam hzroots] at hzg'
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k)
        (m + m) (roots c) x :=
    sixVertexFiniteRootDensity_lower_half_of_weightedGauge hc
      (sixVertexFourierPhysicalDensityMap hc)
      (fun x => hrho c hac.le x) (houter c hac.le)
      (hzg'.trans hio.le)
  refine ⟨roots c,
    ⟨(hrootsData c hcIcc).1, (hrootsData c hcIcc).2, hperron hcIoo⟩, ?_⟩
  simpa [m] using hdensity


theorem eventually_exists_sixVertexFixedEvenChargeBethePerronBranch
    {c : Real} (hc : 2 < c) (s : Nat) :
    ∀ᶠ k : Nat in atTop,
      ∃ p, SixVertexFixedEvenChargePerronBranchWitness c s k p := by
  obtain ⟨_lower, _hlower, h⟩ :=
    eventually_exists_sixVertexFixedEvenChargeBethePerronBranch_with_densityFloor
      hc s
  filter_upwards [h] with k hk
  exact ⟨hk.choose, hk.choose_spec.1⟩


end
end StatMech.FrontierD
