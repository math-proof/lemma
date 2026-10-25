/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part2


namespace StatMech.FrontierD

noncomputable section

theorem abs_weightedFiniteDensity_sub_le_gauge
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    (rho : C(Real, Real))
    (x : Real) (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
    |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤
      sixVertexWeightedFiniteDensityGauge hc N n p rho := by
  simpa only [sixVertexWeightedFiniteDensityGauge,
    sixVertexWeightedFiniteDensityDifference, Real.norm_eq_abs] using
    (sixVertexWeightedFiniteDensityDifference hc N n p rho).norm_coe_le_norm
      ⟨x, hx⟩

theorem sixVertexWeightedFiniteDensityGauge_le_of_pointwise
    {c : Real} (hc : 2 < c) {N n : Nat} (p : Fin n → Real)
    (rho : C(Real, Real)) {E : Real} (hE : 0 ≤ E)
    (hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |sixVertexRootDensityWeight c x *
        (sixVertexFiniteRootDensity c N n p x - rho x)| ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N n p rho ≤ E := by
  rw [sixVertexWeightedFiniteDensityGauge,
    ContinuousMap.norm_le _ hE]
  intro x
  simpa only [sixVertexWeightedFiniteDensityDifference, Real.norm_eq_abs] using
    hbound x x.2

theorem sixVertexWeightedFiniteDensityGauge_selfImproves
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {lower E : Real} (hlower : 0 < lower)
    (hdensity : ∀ x, lower ≤ sixVertexFiniteRootDensity c N (n + 1) p x)
    (hE : 0 ≤ E)
    (hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤ E) :
    sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      sixVertexRootDensityContractionRate c * E +
        sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
  have hrate := sixVertexRootDensityContractionRate_mem_Ico hc
  have hkernel : 0 < sixVertexRootDensityKernelLipschitzBound c :=
    sixVertexRootDensityKernelLipschitzBound_pos hc
  have huniform : 0 < sixVertexFiniteRootDensityUniformBound c := by
    unfold sixVertexFiniteRootDensityUniformBound
    have hd := one_lt_sixVertexAnisotropyMagnitude hc
    positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have herror : 0 ≤ sixVertexFiniteDensityContinuumErrorOfLower c N lower := by
    unfold sixVertexFiniteDensityContinuumErrorOfLower
    positivity
  apply sixVertexWeightedFiniteDensityGauge_le_of_pointwise hc p rho
    (add_nonneg (mul_nonneg hrate.1 hE) herror)
  intro x hx
  apply abs_finiteRootDensity_sub_continuumDensity_weighted_le_of_lower
    hc hN hcount hhalf hopen hsol rho.continuous hrhoEq hrhoMass hlower
    hdensity hE _ x hx
  intro y hy
  exact (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy).trans hgauge

theorem sixVertexWeightedFiniteDensityGauge_solutionFreeAnnulus
    {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N)
    (hcount : n + 1 ≤ N) (hhalf : N = 2 * (n + 1))
    {p : Fin (n + 1) → Real}
    (hopen : SixVertexOpenRootSimplex p)
    (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
    (rho : C(Real, Real))
    (hrhoEq : SixVertexSatisfiesContinuousDensityEquation c rho)
    (hrhoMass : ∫ y in -Real.pi..Real.pi, rho y = 1 / 2)
    {rhoLower inner outer : Real} (hrhoLower : 0 < rhoLower)
    (hrho : ∀ x, rhoLower ≤ rho x)
    (houter : outer ≤ rhoLower *
      ((sixVertexAnisotropyMagnitude c - 1) /
        sixVertexRootDensityScale c) / 2)
    (hinner : sixVertexRootDensityContractionRate c * outer +
        sixVertexFiniteDensityContinuumErrorOfLower c N (rhoLower / 2) ≤
      inner) :
    ¬(inner < sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ∧
      sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho < outer) := by
  rintro ⟨hinnerGauge, hgaugeOuter⟩
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hgauge : sixVertexWeightedFiniteDensityGauge hc N (n + 1) p rho ≤
      outer := hgaugeOuter.le
  have houterNonneg : 0 ≤ outer :=
    (norm_nonneg (sixVertexWeightedFiniteDensityDifference
      hc N (n + 1) p rho)).trans hgauge
  have hdensity : ∀ x, rhoLower / 2 ≤
      sixVertexFiniteRootDensity c N (n + 1) p x := by
    intro x
    obtain ⟨y, hy, hxy⟩ :=
      (periodic_sixVertexFiniteRootDensity c N (n + 1) p).exists_mem_Ioc
        (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
    have hy' : y ∈ Set.Icc (-Real.pi) Real.pi := by
      constructor
      · exact hy.1.le
      · calc
          y ≤ -Real.pi + 2 * Real.pi := hy.2
          _ = Real.pi := by ring
    have hyclose :=
      (abs_weightedFiniteDensity_sub_le_gauge hc p rho y hy').trans hgauge
    have hx := sixVertexFiniteRootDensity_lower_at_of_weighted_close
      hc p (hrho y) hyclose
    change rhoLower - outer / wmin ≤ _ at hx
    have houter' : outer ≤ rhoLower * wmin / 2 := by
      simpa [wmin] using houter
    have hquot : outer / wmin ≤ rhoLower / 2 := by
      rw [div_le_iff₀ hwmin]
      nlinarith
    rw [hxy]
    linarith
  have himprove := sixVertexWeightedFiniteDensityGauge_selfImproves
    hc hN hcount hhalf hopen hsol rho hrhoEq hrhoMass
      (by linarith : 0 < rhoLower / 2) hdensity houterNonneg hgauge
  linarith

end
end StatMech.FrontierD
