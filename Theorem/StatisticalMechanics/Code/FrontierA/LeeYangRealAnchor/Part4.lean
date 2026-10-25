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
import Def.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part4
open Filter Set Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.FK StatMech.Lattice


theorem leeYangRightRealAnchor_subset_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) :
    leeYangRightRealAnchor d hd beta ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  exact hz.2.1


theorem leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    {z : ℂ} (hz : z ∈ leeYangRightRealAnchor d hd beta) :
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


theorem leeYangRightRealAnchor_frequently_near
    (d : ℕ) (hd : 1 ≤ d) (beta h₀ : ℝ) (hh₀ : 0 < h₀) :
    ∃ᶠ z in nhdsWithin (h₀ : ℂ) ({(h₀ : ℂ)}ᶜ),
      z ∈ leeYangRightRealAnchor d hd beta := by
  have hregularDense : Dense (leeYangPressureRegularRealSet d hd beta) := by
    have h := (leeYangPressureRegularRealSet_countable_compl d hd beta).dense_compl ℝ
    simpa only [compl_compl] using h
  have hclosure : (h₀ : ℂ) ∈
      closure (leeYangRightRealAnchor d hd beta \ {(h₀ : ℂ)}) := by
    refine mem_closure_iff.2 ?_
    intro U hUopen hhU
    let W : Set ℝ := ((Complex.ofReal ⁻¹' U) ∩ Ioi 0) \ {h₀}
    have hWopen : IsOpen W := by
      exact ((hUopen.preimage Complex.continuous_ofReal).inter isOpen_Ioi).sdiff
        isClosed_singleton
    have hbase : (Complex.ofReal ⁻¹' U) ∩ Ioi 0 ∈ nhds h₀ :=
      Filter.inter_mem
        ((hUopen.preimage Complex.continuous_ofReal).mem_nhds hhU)
        (isOpen_Ioi.mem_nhds hh₀)
    have hWnonempty : W.Nonempty := by
      obtain ⟨l, u, hlu, hsub⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp hbase
      obtain ⟨y, hh₀y, hyu⟩ := exists_between hlu.2
      have hybase : y ∈ (Complex.ofReal ⁻¹' U) ∩ Ioi 0 :=
        hsub ⟨hlu.1.trans hh₀y, hyu⟩
      exact ⟨y, hybase, by simpa using ne_of_gt hh₀y⟩
    obtain ⟨y, hyW, hyregular⟩ :=
      hregularDense.inter_open_nonempty W hWopen hWnonempty
    refine ⟨(y : ℂ), hyW.1.1, ?_⟩
    constructor
    · exact ⟨by simp, hyW.1.2, hyregular⟩
    · simpa using hyW.2
  rw [frequently_nhdsWithin_iff]
  exact (mem_closure_iff_frequently.mp hclosure).mono fun z hz =>
    ⟨hz.1, hz.2⟩


theorem leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta)
    (hcompact : IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | 0 < z.re}) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | 0 < z.re} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  let U : Set ℂ := {z | 0 < z.re}
  let anchor := leeYangRightRealAnchor d hd beta
  let anchorLimit : ℂ → ℂ := fun z =>
    (pressureRightDeriv (isingBoxPressureLimit d hd beta) z.re : ℂ)
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconnected : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hholomorphic : ∀ n, DifferentiableOn ℂ (F n) U :=
    (leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane
      d hbeta).1
  have hanchorLimit : ∀ z ∈ anchor,
      Tendsto (fun n => F n z) atTop (nhds (anchorLimit z)) := by
    intro z hz
    exact leeYangBox_normalizedFieldLogDerivative_tendsto_rightRealAnchor
      d hd beta hz
  simpa only [F, U, anchor, anchorLimit] using
    montelVitali_of_locallyUniform_precompact
      F U anchor (1 : ℂ) anchorLimit hUopen hUconnected
      (by change 0 < (1 : ℂ).re; norm_num)
      (leeYangRightRealAnchor_subset_rightHalfPlane d hd beta)
      (by simpa using leeYangRightRealAnchor_frequently_near d hd beta 1 zero_lt_one)
      hholomorphic hcompact hanchorLimit


end StatMech.FrontierA
