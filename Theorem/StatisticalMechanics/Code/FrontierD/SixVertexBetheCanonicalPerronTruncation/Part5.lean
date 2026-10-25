/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part5
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope
    {c : Real} (hc0 : c ≠ 0) :
    Tendsto (sixVertexCanonicalRegularizationDiagonalEnvelope c)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let C : Real := Real.log (c ^ 2 / 2) + 1
  have hid : Tendsto (fun eta : Real => eta)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hetalog : Tendsto (fun eta : Real => eta * Real.log eta)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    by
      have hfull : Tendsto (fun eta : Real => eta * Real.log eta)
          (nhds (0 : Real)) (nhds ((0 : Real) * Real.log 0)) :=
        Real.continuous_mul_log.continuousAt.tendsto
      simpa using hfull.mono_left inf_le_left
  have hmain : Tendsto (fun eta : Real =>
      2 * eta * (C - Real.log eta) + eta / 4)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hlinear := hid.const_mul (2 * C)
    have hlog := hetalog.const_mul 2
    have hsmall := hid.const_mul (1 / 4 : Real)
    convert (hlinear.sub hlog).add hsmall using 1
    · funext eta
      ring
    · norm_num
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  have hetaPos : 0 < eta := heta
  have hconst : c ^ 2 / 2 ≠ 0 := by positivity
  unfold sixVertexCanonicalRegularizationDiagonalEnvelope
    sixVertexCanonicalRegularizationEnvelope
  rw [show c ^ 2 / (2 * eta) = (c ^ 2 / 2) / eta by ring,
    Real.log_div hconst hetaPos.ne']
  dsimp [C]
  field_simp [hetaPos.ne']
  ring


theorem eventually_exists_sixVertexCanonicalRegularizedApproximation
    {c : Real} (hc : 2 < c) {delta : Real} (hdelta : 0 < delta) :
    ∃ eta : Real, 0 < eta ∧ eta <= 1 / 4 ∧
      eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4 ∧
      ∀ᶠ k : Nat in atTop,
        sixVertexSymmetricBetheRootAverage c
            (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k -
          sixVertexCanonicalDensityPerronEmpiricalObservable hc
            (sixVertexRegularizedBetheLogKernel c (eta ^ 2)) k < delta := by
  let D : Real := (c ^ 2 - 2) ^ 2 - 4
  have hc2 : 2 < c ^ 2 - 2 := by
    nlinarith [sq_nonneg (c - 2)]
  have hD : 0 < D := by dsimp [D]; nlinarith
  let a : Real := min (1 / 4) (min 1 D)
  have ha : 0 < a := by dsimp [a]; positivity
  have henv : ∀ᶠ eta : Real in nhdsWithin 0 (Set.Ioi 0),
      sixVertexCanonicalRegularizationDiagonalEnvelope c eta < delta :=
    (tendsto_sixVertexCanonicalRegularizationDiagonalEnvelope
      (by linarith : c ≠ 0)).eventually (Iio_mem_nhds hdelta)
  have hrange : Set.Ioo (0 : Real) a ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Ioo_mem_nhdsGT ha
  obtain ⟨eta, hetaEnv, hetaRange⟩ :=
    Set.nonempty_def.mp (Filter.nonempty_of_mem (inter_mem henv hrange))
  have heta : 0 < eta := hetaRange.1
  have hetaQuarter : eta <= 1 / 4 :=
    hetaRange.2.le.trans (min_le_left _ _)
  have hetaOne : eta <= 1 :=
    hetaRange.2.le.trans (min_le_right _ _ |>.trans (min_le_left _ _))
  have hetaD : eta <= D :=
    hetaRange.2.le.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  have hetaSq : eta ^ 2 <= D := by
    have : eta ^ 2 <= eta := by nlinarith
    exact this.trans hetaD
  refine ⟨eta, heta, hetaQuarter, by simpa only [D] using hetaSq, ?_⟩
  have hupper := tendsto_sixVertexCanonicalRegularizationUpper
    (c := c) (epsilon := eta ^ 2) (by linarith : c ≠ 0) heta
  have hupperEventually : ∀ᶠ k : Nat in atTop,
      sixVertexCanonicalRegularizationUpper c (eta ^ 2) eta k < delta :=
    hupper.eventually (Iio_mem_nhds hetaEnv)
  filter_upwards [hupperEventually] with k hk
  exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
    hc (sq_pos_of_pos heta) (by simpa only [D] using hetaSq)
    heta hetaQuarter k).trans_lt hk


theorem tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c epsilon)) atTop
      (nhds (∫ y in -Real.pi..Real.pi,
        sixVertexRegularizedBetheLogKernel c epsilon y *
          sixVertexFourierPhysicalDensity c hc y)) := by
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  have hf : Continuous f :=
    continuous_sixVertexRegularizedBetheLogKernel hc hepsilon
  obtain ⟨C, hC⟩ :=
    exists_lipschitzWith_sixVertexRegularizedBetheLogKernel hc hepsilon
  let B : Real := |f 0| + (C : Real) * Real.pi
  have hbound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B := by
    intro x hx
    have hdist : |f x - f 0| <= (C : Real) * |x| := by
      simpa only [Real.norm_eq_abs, sub_zero] using hC.norm_sub_le x 0
    have hxabs : |x| <= Real.pi := abs_le.mpr hx
    calc
      |f x| = |(f x - f 0) + f 0| := by ring_nf
      _ <= |f x - f 0| + |f 0| := abs_add_le _ _
      _ <= (C : Real) * |x| + |f 0| := by linarith
      _ <= (C : Real) * Real.pi + |f 0| := by
        gcongr
      _ = B := by dsimp [B]; ring
  have hBnonneg : 0 <= B := by
    dsimp [B]
    positivity
  exact tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable hc
    hf hC (periodic_sixVertexRegularizedBetheLogKernel c epsilon)
    hBnonneg hbound


theorem cauchySeq_sixVertexCanonicalDensityPerronRootAverage
    {c : Real} (hc : 2 < c) :
    CauchySeq (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)) := by
  rw [Metric.cauchySeq_iff]
  intro delta hdelta
  obtain ⟨eta, heta, hetaQuarter, hetaSq, happ⟩ :=
    eventually_exists_sixVertexCanonicalRegularizedApproximation hc
      (delta := delta / 3) (by positivity)
  let raw : Nat -> Real := sixVertexSymmetricBetheRootAverage c
    (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)
  let reg : Nat -> Real :=
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c (eta ^ 2))
  have hregT : Tendsto reg atTop (nhds (∫ y in -Real.pi..Real.pi,
      sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
        sixVertexFourierPhysicalDensity c hc y)) :=
    tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel hc
      (sq_pos_of_pos heta)
  have hregC : CauchySeq reg := hregT.cauchySeq
  rw [Metric.cauchySeq_iff] at hregC
  obtain ⟨Nreg, hNreg⟩ := hregC (delta / 3) (by positivity)
  obtain ⟨Napp, hNapp⟩ := eventually_atTop.1 happ
  refine ⟨max Nreg Napp, ?_⟩
  intro m hm n hn
  have hmReg : Nreg <= m := (le_max_left _ _).trans hm
  have hnReg : Nreg <= n := (le_max_left _ _).trans hn
  have hmApp : Napp <= m := (le_max_right _ _).trans hm
  have hnApp : Napp <= n := (le_max_right _ _).trans hn
  have hmClose : raw m - reg m < delta / 3 := hNapp m hmApp
  have hnClose : raw n - reg n < delta / 3 := hNapp n hnApp
  have hmNonneg : 0 <= raw m - reg m := by
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta m) m).1
  have hnNonneg : 0 <= raw n - reg n := by
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta n) n).1
  have hregClose : dist (reg m) (reg n) < delta / 3 :=
    hNreg m hmReg n hnReg
  have hmDist : dist (raw m) (reg m) < delta / 3 := by
    rw [Real.dist_eq, abs_of_nonneg hmNonneg]
    exact hmClose
  have hnDist : dist (reg n) (raw n) < delta / 3 := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hnNonneg]
    exact hnClose
  calc
    dist (raw m) (raw n) <=
        dist (raw m) (reg m) + dist (reg m) (raw n) := dist_triangle _ _ _
    _ <= dist (raw m) (reg m) +
        (dist (reg m) (reg n) + dist (reg n) (raw n)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < delta := by linarith


theorem exists_sixVertexCanonicalDensityPerronRootAverage_limit
    {c : Real} (hc : 2 < c) :
    ∃ a : Real, Tendsto (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc))
        atTop (nhds a) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_sixVertexCanonicalDensityPerronRootAverage hc)

end
end StatMech.FrontierD
