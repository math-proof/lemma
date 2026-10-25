/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
    {c : Real} (hc : 2 < c) {f : Real → Real} {B : Real}
    (hf : Continuous f) (hB : 0 ≤ B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B)
    (k : Nat) :
    |(∫ y in -Real.pi..Real.pi,
          f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
            ((k + 1) + (k + 1))
            (sixVertexCanonicalDensityPerronBetheRoots hc k) y) -
        ∫ y in -Real.pi..Real.pi,
          f y * sixVertexFourierPhysicalDensity c hc y| ≤
      B * (sixVertexCanonicalDensityPerronGauge hc k /
        ((sixVertexAnisotropyMagnitude c - 1) /
          sixVertexRootDensityScale c)) * (2 * Real.pi) := by
  let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
    ((k + 1) + (k + 1))
    (sixVertexCanonicalDensityPerronBetheRoots hc k)
  let rho := sixVertexFourierPhysicalDensity c hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  let gauge := sixVertexCanonicalDensityPerronGauge hc k
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  have hrhoN : Continuous rhoN :=
    continuous_sixVertexFiniteRootDensity hc _ _ _
  have hrho : Continuous rho := continuous_sixVertexFourierPhysicalDensity hc
  have hIN : IntervalIntegrable (fun y => f y * rhoN y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrhoN).intervalIntegrable _ _
  have hI : IntervalIntegrable (fun y => f y * rho y)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    (hf.mul hrho).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hIN hI]
  have hnorm :
      ‖∫ y in -Real.pi..Real.pi,
          (f y * rhoN y - f y * rho y)‖ ≤
        (B * (gauge / wmin)) * |Real.pi - -Real.pi| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hyIcc : y ∈ Set.Icc (-Real.pi) Real.pi := by
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hy
      exact ⟨hy.1.le, hy.2⟩
    have hpoint := abs_weightedFiniteDensity_sub_le_gauge hc
      (N := sixVertexFourWidth 0 k)
      (sixVertexCanonicalDensityPerronBetheRoots hc k)
      (sixVertexFourierPhysicalDensityMap hc) y hyIcc
    have hdiff : |rhoN y - rho y| ≤ gauge / wmin := by
      rw [le_div_iff₀ hwmin]
      calc
        |rhoN y - rho y| * wmin ≤
            |rhoN y - rho y| * sixVertexRootDensityWeight c y := by
          gcongr
          exact sixVertexRootDensityWeight_lower hc y
        _ = |sixVertexRootDensityWeight c y * (rhoN y - rho y)| := by
          rw [abs_mul, abs_of_pos (sixVertexRootDensityWeight_pos hc y)]
          ring
        _ ≤ gauge := by
          simpa only [rhoN, rho, gauge,
            sixVertexCanonicalDensityPerronGauge,
            sixVertexFourierPhysicalDensityMap] using hpoint
    calc
      ‖f y * rhoN y - f y * rho y‖ =
          |f y| * |rhoN y - rho y| := by
        rw [show f y * rhoN y - f y * rho y =
          f y * (rhoN y - rho y) by ring]
        simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ B * (gauge / wmin) :=
        mul_le_mul (hfBound y hyIcc) hdiff (abs_nonneg _)
          hB
  rw [Real.norm_eq_abs] at hnorm
  rw [abs_of_pos (by nlinarith [Real.pi_pos] :
    0 < Real.pi - -Real.pi)] at hnorm
  dsimp only [rhoN, rho, gauge, wmin] at hnorm
  convert hnorm using 1 <;> ring


theorem tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable
    {c : Real} (hc : 2 < c)
    {f : Real → Real} {C : NNReal} {B : Real}
    (hf : Continuous f) (hlip : LipschitzWith C f)
    (hperiodic : Function.Periodic f (2 * Real.pi))
    (hB : 0 ≤ B)
    (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B) :
    Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc f)
      atTop (nhds (∫ y in -Real.pi..Real.pi,
        f y * sixVertexFourierPhysicalDensity c hc y)) := by
  obtain ⟨lower, hlower, hdensity⟩ :=
    eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc
  let wmin := (sixVertexAnisotropyMagnitude c - 1) /
    sixVertexRootDensityScale c
  have hwmin : 0 < wmin := by
    dsimp [wmin]
    exact div_pos (sub_pos.mpr (one_lt_sixVertexAnisotropyMagnitude hc))
      (sixVertexRootDensityScale_pos hc)
  let qerr : Nat → Real := fun k =>
    (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      (1 / ((sixVertexFourWidth 0 k : Real) * lower)) * (2 * Real.pi)
  let derr : Nat → Real := fun k =>
    B * (sixVertexCanonicalDensityPerronGauge hc k / wmin) * (2 * Real.pi)
  have hwidth : Tendsto (sixVertexFourWidth 0) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro N
    refine ⟨N, ?_⟩
    intro k hk
    unfold sixVertexFourWidth
    omega
  have hwidthReal : Tendsto (fun k =>
      (sixVertexFourWidth 0 k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidth
  let Q := (C : Real) * sixVertexFiniteRootDensityUniformBound c *
    (1 / lower) * (2 * Real.pi)
  have hqerr : Tendsto qerr atTop (nhds 0) := by
    have h := hwidthReal.const_div_atTop Q
    convert h using 1
    funext k
    dsimp [qerr, Q]
    field_simp [hlower.ne']
  have hderr : Tendsto derr atTop (nhds 0) := by
    have h := (((tendsto_sixVertexCanonicalDensityPerronGauge hc).div_const
      wmin).const_mul B).mul_const (2 * Real.pi)
    simpa only [derr, zero_div, zero_mul, mul_zero] using h
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  apply squeeze_zero'
  · filter_upwards [] with k
    exact norm_nonneg _
  · filter_upwards [hdensity] with k hkDensity
    let p := sixVertexCanonicalDensityPerronBetheRoots hc k
    let rhoN := sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k)
      ((k + 1) + (k + 1)) p
    let I := ∫ y in -Real.pi..Real.pi, f y * rhoN y
    let target := ∫ y in -Real.pi..Real.pi,
      f y * sixVertexFourierPhysicalDensity c hc y
    have hN : 0 < sixVertexFourWidth 0 k := sixVertexFourWidth_pos 0 k
    have hn : 0 < (k + 1) + (k + 1) := by omega
    have hhalf : sixVertexFourWidth 0 k =
        2 * ((k + 1) + (k + 1)) := by
      unfold sixVertexFourWidth
      omega
    have hquad :=
      abs_empiricalPeriodicLipschitz_sub_finiteDensityIntegral_of_lower
        hc hN hn hhalf (sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k)
        (sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k)
        hlower hkDensity hf hlip hperiodic
    have hint := abs_sixVertexCanonicalDensityIntegral_sub_fourier_le
      hc hf hB hfBound k
    change |sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - I| ≤
      qerr k at hquad
    change |I - target| ≤ derr k at hint
    change ‖sixVertexCanonicalDensityPerronEmpiricalObservable hc f k - target‖ ≤
      qerr k + derr k
    rw [Real.norm_eq_abs]
    exact (abs_sub_le
      (sixVertexCanonicalDensityPerronEmpiricalObservable hc f k)
      I target).trans (add_le_add hquad hint)
  · simpa only [zero_add] using hqerr.add hderr

end
end StatMech.FrontierD
