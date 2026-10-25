/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangRealAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangNormalFamilyReduction
import Theorem.StatisticalMechanics.Code.Ising.PressureConvex
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.FK.FKPressureDeriv.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


theorem leeYangLeftRealAnchor_subset_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    leeYangLeftRealAnchor d hd beta ⊆ {z : ℂ | z.re < 0} := by
  intro z hz
  exact hz.2.1

theorem leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    {z : ℂ} (hz : z ∈ leeYangLeftRealAnchor d hd beta) :
    Tendsto
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta z)
      atTop
      (nhds (pressureRightDeriv
        (isingBoxPressureLimit d hd beta) z.re : ℂ)) := by
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa using hz.1.symm
  simpa only [hzreal] using
    leeYangBox_normalizedFieldLogDerivative_tendsto_of_regular
      d hd beta z.re hz.2.2

theorem leeYangLeftRealAnchor_frequently_near
    (d : ℕ) (hd : 1 ≤ d) (beta h₀ : ℝ) (hh₀ : h₀ < 0) :
    ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ),
      z ∈ leeYangLeftRealAnchor d hd beta := by
  have hregularDense : Dense (leeYangPressureRegularRealSet d hd beta) := by
    have h := (leeYangPressureRegularRealSet_countable_compl d hd beta).dense_compl ℝ
    simpa only [compl_compl] using h
  have hclosure : (h₀ : ℂ) ∈
      closure (leeYangLeftRealAnchor d hd beta \ {(h₀ : ℂ)}) := by
    refine mem_closure_iff.2 ?_
    intro U hUopen hhU
    let W : Set ℝ := ((Complex.ofReal ⁻¹' U) ∩ Iio 0) \ {h₀}
    have hWopen : IsOpen W := by
      exact ((hUopen.preimage Complex.continuous_ofReal).inter isOpen_Iio).sdiff
        isClosed_singleton
    have hbase : (Complex.ofReal ⁻¹' U) ∩ Iio 0 ∈ nhds h₀ :=
      Filter.inter_mem
        ((hUopen.preimage Complex.continuous_ofReal).mem_nhds hhU)
        (isOpen_Iio.mem_nhds hh₀)
    have hWnonempty : W.Nonempty := by
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp hbase
      obtain ⟨y, hly, hyh₀⟩ := exists_between hlu.1
      have hybase : y ∈ (Complex.ofReal ⁻¹' U) ∩ Iio 0 :=
        hsub ⟨hly, hyh₀.trans hlu.2⟩
      exact ⟨y, hybase, by simpa using ne_of_lt hyh₀⟩
    obtain ⟨y, hyW, hyregular⟩ :=
      hregularDense.inter_open_nonempty W hWopen hWnonempty
    refine ⟨(y : ℂ), hyW.1.1, ?_⟩
    constructor
    · exact ⟨by simp, hyW.1.2, hyregular⟩
    · simpa using hyW.2
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hclosure).mono fun z hz =>
    ⟨hz.1, hz.2⟩


theorem leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | z.re < 0}) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | z.re < 0} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  let U : Set ℂ := {z | z.re < 0}
  let anchor := leeYangLeftRealAnchor d hd beta
  let anchorLimit : ℂ → ℂ := fun z =>
    (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)
  have hUopen : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hUconnected : IsPreconnected U := (convex_halfSpace_re_lt 0).isPreconnected
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U :=
    (leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane
      d hbeta).1
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    exact leeYangBox_normalizedFieldLogDerivative_tendsto_leftRealAnchor
      d hd beta hz
  simpa only [F, U, anchor, anchorLimit] using
    montelVitali_of_locallyUniform_precompact
      F U anchor (-1 : ℂ) anchorLimit hUopen hUconnected
      (by change (-1 : ℂ).re < 0; norm_num)
      (leeYangLeftRealAnchor_subset_leftHalfPlane d hd beta)
      (by simpa using leeYangLeftRealAnchor_frequently_near d hd beta (-1) (by norm_num))
      hholomorphic hcompact hanchorLimit

end StatMech.FrontierA
