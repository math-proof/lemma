/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexWeightedFiniteDensityGauge_fourier_congr
    {c₁ c₂ : Real} (hc₁ : 2 < c₁) (hc₂ : 2 < c₂)
    (hc : c₁ = c₂) {N n : Nat} {p q : Fin n → Real} (hp : p = q) :
    sixVertexWeightedFiniteDensityGauge hc₁ N n p
        (sixVertexFourierPhysicalDensityMap hc₁) =
      sixVertexWeightedFiniteDensityGauge hc₂ N n q
        (sixVertexFourierPhysicalDensityMap hc₂) := by
  subst c₂
  subst q
  rfl


theorem eventually_exists_sixVertexHalfFilledBethePerronBranch
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      ∃ p : Fin ((k + 1) + (k + 1)) → Real,
        SixVertexOpenRootSimplex p ∧
        SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) p ∧
        sixVertexSymmetricBetheEigenvalueKernel c
            (sixVertexEvenPositiveHalfProjection (k + 1) p) =
          sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1)) (by
              unfold sixVertexFourWidth
              omega) c := by
  let a := (2 + c) / 2
  have ha : 2 < a := by dsimp [a]; linarith
  have hac : a < c := by dsimp [a]; linarith
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici ha
  obtain ⟨inner, outer, houterPos, hio, houter, hmargins⟩ :=
    exists_uniform_sixVertexDensityGaugeNumericalMargins_Ici ha hrhoLower
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
      _hrootsGauge⟩ :=
    exists_sixVertexHalfFilledPerronSheet_of_densityGauge
      ha (by dsimp [b]; linarith) hc₀Ioo k
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
      hz₀g (hc₀Cand (ha.trans hc₀Ioo.1)).1
      (hc₀Cand (ha.trans hc₀Ioo.1)).2
  refine ⟨roots c, (hrootsData c hcIcc).1, (hrootsData c hcIcc).2, ?_⟩
  exact hperron hcIoo


end
end StatMech.FrontierD
