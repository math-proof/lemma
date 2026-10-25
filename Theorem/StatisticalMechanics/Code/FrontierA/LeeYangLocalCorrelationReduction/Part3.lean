/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part3
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


theorem leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d))
    (hpoint : LeeYangSpinProductRightBound d beta A)
    {K : Set ℂ} (hK : IsCompact K) (hKright : K ⊆ {h : ℂ | 0 < h.re}) :
    ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangSpinProductRightEnvelope hbeta A).mono hKright)
  refine ⟨C, fun n h hh => ?_⟩
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
        leeYangSpinProductRightEnvelope beta A h := hpoint n h (hKright hh)
    _ ≤ ‖leeYangSpinProductRightEnvelope beta A h‖ := Real.le_norm_self _
    _ ≤ C := hC h hh

theorem leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d))
    (hpoint : LeeYangSpinProductLeftBound d beta A)
    {K : Set ℂ} (hK : IsCompact K) (hKleft : K ⊆ {h : ℂ | h.re < 0}) :
    ∃ C : ℝ, ∀ n h, h ∈ K → ‖leeYangBoxSpinProduct d beta A n h‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_leeYangSpinProductLeftEnvelope hbeta A).mono hKleft)
  refine ⟨C, fun n h hh => ?_⟩
  calc
    ‖leeYangBoxSpinProduct d beta A n h‖ ≤
        leeYangSpinProductLeftEnvelope beta A h := hpoint n h (hKleft hh)
    _ ≤ ‖leeYangSpinProductLeftEnvelope beta A h‖ := Real.le_norm_self _
    _ ≤ C := hC h hh


theorem leeYangBoxSpinProduct_rightHalfPlane_of_pointwiseBound
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d))
    (hpoint : LeeYangSpinProductRightBound d beta A) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | 0 < z.re} := by
  let F := leeYangBoxSpinProduct d beta A
  let U : Set ℂ := {z | 0 < z.re}
  let anchor : Set ℂ := {z | z.im = 0 ∧ 0 < z.re}
  let anchorLimit : ℂ → ℂ := fun z => Complex.ofReal
    (∫ omega, spinProd A omega
      ∂(freeState d beta z.re : Measure (ConfigSpace (Site d))))
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U := fun n =>
    (leeYangBoxSpinProduct_analyticOnNhd_rightHalfPlane
      d n hbeta.le A).differentiableOn
  have hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C := by
    intro K hK hKU
    exact leeYangBoxSpinProduct_boundedOn_compact_rightHalfPlane
      d hbeta A hpoint hK hKU
  have hcompact : IsLocallyUniformlySequentiallyPrecompact F U :=
    holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hholomorphic hbounded rightHalfPlaneCompactExhaustion
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simpa using hz.1.symm
    simpa only [F, anchorLimit, hzreal] using
      leeYangBoxSpinProduct_tendsto_of_nonneg_real_field
        d beta z.re hbeta.le hz.2.le A
  have haccum : ∃ᶠ z in nhdsWithin (1 : ℂ) ({(1 : ℂ)}ᶜ), z ∈ anchor :=
    (leeYangRightRealAnchor_frequently_near d hd beta 1 zero_lt_one).mono
      fun z hz => ⟨hz.1, hz.2.1⟩
  simpa only [F, U] using
    montelVitali_of_locallyUniform_precompact F U anchor (1 : ℂ) anchorLimit
      hUopen (convex_halfSpace_re_gt 0).isPreconnected
      (by change 0 < (1 : ℂ).re; norm_num)
      (fun _ hz => hz.2) haccum hholomorphic hcompact hanchorLimit


theorem leeYangBoxSpinProduct_leftHalfPlane_of_pointwiseBound
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (A : Finset (Site d))
    (hpoint : LeeYangSpinProductLeftBound d beta A) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn (leeYangBoxSpinProduct d beta A) g
        atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ leeYangBoxSpinProduct d beta A) (deriv g)
        atTop {z : ℂ | z.re < 0} := by
  let F := leeYangBoxSpinProduct d beta A
  let U : Set ℂ := {z | z.re < 0}
  let anchor : Set ℂ := {z | z.im = 0 ∧ z.re < 0}
  let anchorLimit : ℂ → ℂ := fun z => (((-1 : ℝ) : ℂ) ^ A.card) *
    Complex.ofReal (∫ omega, spinProd A omega
      ∂(freeState d beta (-z.re) : Measure (ConfigSpace (Site d))))
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U := fun n =>
    (leeYangBoxSpinProduct_analyticOnNhd_leftHalfPlane
      d n hbeta.le A).differentiableOn
  have hbounded : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ C : ℝ, ∀ n z, z ∈ K → ‖F n z‖ ≤ C := by
    intro K hK hKU
    exact leeYangBoxSpinProduct_boundedOn_compact_leftHalfPlane
      d hbeta A hpoint hK hKU
  have hcompact : IsLocallyUniformlySequentiallyPrecompact F U :=
    holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
      F U hUopen hholomorphic hbounded leftHalfPlaneCompactExhaustion
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    have hzreal : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · simpa using hz.1.symm
    simpa only [F, anchorLimit, hzreal] using
      leeYangBoxSpinProduct_tendsto_of_neg_real_field
        d beta z.re hbeta.le hz.2 A
  have hfreq := leeYangLeftRealAnchor_frequently_near
    d hd beta (-1 : ℝ) (by norm_num)
  have haccum : ∃ᶠ z in nhdsWithin ((-1 : ℝ) : ℂ) ({((-1 : ℝ) : ℂ)}ᶜ),
      z ∈ anchor := hfreq.mono fun z hz =>
    (show z.im = 0 ∧ z.re < 0 from ⟨hz.1, hz.2.1⟩)
  simpa only [F, U] using
    montelVitali_of_locallyUniform_precompact F U anchor ((-1 : ℝ) : ℂ) anchorLimit
      hUopen (convex_halfSpace_re_lt 0).isPreconnected
      (by change (((-1 : ℝ) : ℂ)).re < 0; norm_num)
      (fun _ hz => hz.2) haccum hholomorphic hcompact hanchorLimit


theorem multiAffine_sign_update_norm_le
    {I : Type*} [DecidableEq I]
    (p : (I → ℂ) → ℂ) (hpAff : IsMultiAffine p)
    (hpStable : PolydiscStable p) (z : I → ℂ)
    (hz : ∀ j, ‖z j‖ < 1) (i : I) :
    ‖p (Function.update z i (-z i))‖ ≤
      ((1 + ‖z i‖) / (1 - ‖z i‖)) * ‖p z‖ := by
  let a := p (Function.update z i 0)
  let b := p (Function.update z i 1) - p (Function.update z i 0)
  have hp (t : ℂ) : p (Function.update z i t) = a + t * b := by
    simpa only [a, b] using hpAff i z t
  have hpz : p z = a + z i * b := by
    have hu : Function.update z i (z i) = z := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    calc
      p z = p (Function.update z i (z i)) := congrArg p hu.symm
      _ = a + z i * b := hp _
  have hpneg : p (Function.update z i (-z i)) = a + (-z i) * b := hp _
  have hba : ‖b‖ ≤ ‖a‖ := by
    by_contra hnot
    have hab : ‖a‖ < ‖b‖ := lt_of_not_ge hnot
    have hb0 : b ≠ 0 := by
      intro hb
      rw [hb, norm_zero] at hab
      exact (not_lt_of_ge (norm_nonneg a)) hab
    let t : ℂ := -a / b
    have ht : ‖t‖ < 1 := by
      simp only [t, norm_div, norm_neg]
      exact (div_lt_one (norm_pos_iff.mpr hb0)).2 hab
    have hzu : ∀ j, ‖Function.update z i t j‖ < 1 := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ht
      · simpa [hji] using hz j
    apply hpStable (Function.update z i t) hzu
    rw [hp]
    dsimp only [t]
    field_simp [hb0]
    ring
  have hnum : ‖p (Function.update z i (-z i))‖ ≤
      ‖a‖ + ‖z i‖ * ‖b‖ := by
    rw [hpneg]
    calc
      ‖a + -z i * b‖ ≤ ‖a‖ + ‖-z i * b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖z i‖ * ‖b‖ := by rw [norm_mul, norm_neg]
  have hden : ‖a‖ - ‖z i‖ * ‖b‖ ≤ ‖p z‖ := by
    rw [hpz]
    calc
      ‖a‖ - ‖z i‖ * ‖b‖ = ‖a‖ - ‖-(z i * b)‖ := by
        rw [norm_neg, norm_mul]
      _ ≤ ‖a - -(z i * b)‖ := norm_sub_norm_le a (-(z i * b))
      _ = ‖a + z i * b‖ := by ring_nf
  have hzi0 : 0 ≤ ‖z i‖ := norm_nonneg _
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖b‖ := norm_nonneg _
  have hden0 : 0 ≤ ‖p z‖ := norm_nonneg _
  have hcross :
      ‖p (Function.update z i (-z i))‖ * (1 - ‖z i‖) ≤
        (1 + ‖z i‖) * ‖p z‖ := by
    nlinarith [hz i]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr (hz i))).2 hcross


end StatMech.FrontierA
