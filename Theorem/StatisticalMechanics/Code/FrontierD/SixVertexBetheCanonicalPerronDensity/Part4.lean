/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalDensityPerronGauge hc k <
        (1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8 := by
  filter_upwards
    [eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hk
  exact hk.2

theorem tendsto_sixVertexCanonicalDensityPerronGauge
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCanonicalDensityPerronGauge hc) atTop (nhds 0) := by
  have hstageReal : Tendsto (fun k =>
      (sixVertexPerronGaugeStage hc k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sixVertexPerronGaugeStage hc)
  have hupper : Tendsto (fun k =>
      (1 : Real) / sixVertexPerronGaugeStage hc k) atTop (nhds 0) :=
    hstageReal.const_div_atTop 1
  have hstagePos : ∀ᶠ k : Nat in atTop,
      0 < sixVertexPerronGaugeStage hc k :=
    (tendsto_sixVertexPerronGaugeStage hc).eventually
      (eventually_gt_atTop 0)
  apply squeeze_zero'
  · filter_upwards [] with k
    exact norm_nonneg _
  · filter_upwards
      [hstagePos,
        eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hkPos hk
    have hstage : (1 : Real) ≤ sixVertexPerronGaugeStage hc k := by
      exact_mod_cast hkPos
    have hpow : (sixVertexPerronGaugeStage hc k : Real) ≤
        (sixVertexPerronGaugeStage hc k : Real) ^ 8 := by
      simpa using pow_le_pow_right₀ hstage (show 1 ≤ 8 by omega)
    exact hk.2.le.trans (by
      apply one_div_le_one_div_of_le (a :=
        (sixVertexPerronGaugeStage hc k : Real)) (by positivity)
      exact hpow)
  · exact hupper


theorem eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower
    {c : Real} (hc : 2 < c) :
    ∃ lower : Real, 0 < lower ∧
      ∀ᶠ k : Nat in atTop, ∀ x : Real,
        lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1))
          (sixVertexCanonicalDensityPerronBetheRoots hc k) x := by
  obtain ⟨rhoLower, hrhoLower, hrho⟩ :=
    exists_uniformLower_sixVertexFourierPhysicalDensity_Ici hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  let lower := rhoLower / 2
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have htarget : 0 < rhoLower * wmin / 2 := by positivity
  have hgauge : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalDensityPerronGauge hc k < rhoLower * wmin / 2 :=
    (tendsto_sixVertexCanonicalDensityPerronGauge hc).eventually
      (Iio_mem_nhds htarget)
  refine ⟨lower, hlower, ?_⟩
  filter_upwards [hgauge] with k hk
  intro x
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1))
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
  let rho := sixVertexFourierPhysicalDensity c hc
  obtain ⟨y, hy, hxy⟩ :=
    (periodic_sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1))
      (sixVertexCanonicalDensityPerronBetheRoots hc k)).exists_mem_Ioc
        (by positivity : 0 < 2 * Real.pi) x (-Real.pi)
  have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
    exact ⟨hy.1.le, by linarith [hy.2]⟩
  have hpoint := abs_weightedFiniteDensity_sub_le_gauge hc
    (N := sixVertexFourWidth 0 k)
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
    (sixVertexFourierPhysicalDensityMap hc)
    y hyIcc
  have hweighted : wmin * |rhoN y - rho y| < rhoLower * wmin / 2 := by
    calc
      wmin * |rhoN y - rho y| ≤
          sixVertexRootDensityWeight c y * |rhoN y - rho y| := by
        gcongr
        exact sixVertexRootDensityWeight_lower hc y
      _ = |sixVertexRootDensityWeight c y * (rhoN y - rho y)| := by
        rw [abs_mul, abs_of_pos (sixVertexRootDensityWeight_pos hc y)]
      _ ≤ sixVertexCanonicalDensityPerronGauge hc k := by
        simpa only [sixVertexCanonicalDensityPerronGauge, rhoN, rho,
          sixVertexFourierPhysicalDensityMap] using hpoint
      _ < rhoLower * wmin / 2 := hk
  have hdiff : |rhoN y - rho y| < rhoLower / 2 := by
    have hweighted' : wmin * |rhoN y - rho y| <
        wmin * (rhoLower / 2) := by
      convert hweighted using 1 <;> ring
    exact lt_of_mul_lt_mul_left hweighted' hwmin.le
  have hrho : rhoLower ≤ rho y := hrho c le_rfl y
  dsimp [lower]
  rw [hxy]
  linarith [neg_abs_le (rhoN y - rho y)]

end
end StatMech.FrontierD
