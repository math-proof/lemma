/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexCanonicalDensityPerronRootAverage
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexSymmetricBetheRootAverage c
      (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc))
        atTop (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) :=
  Classical.choose_spec
    (exists_sixVertexCanonicalDensityPerronRootAverage_limit hc)


theorem abs_sixVertexCanonicalDensityPerronRootAverageLimit_sub_regularizedIntegral_le
    {c eta : Real} (hc : 2 < c) (heta : 0 < eta)
    (hetaQuarter : eta <= 1 / 4)
    (hetaSq : eta ^ 2 <= (c ^ 2 - 2) ^ 2 - 4) :
    |sixVertexCanonicalDensityPerronRootAverageLimit hc -
        ∫ y in -Real.pi..Real.pi,
          sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
            sixVertexFourierPhysicalDensity c hc y| <=
      sixVertexCanonicalRegularizationDiagonalEnvelope c eta := by
  let raw : Nat -> Real := sixVertexSymmetricBetheRootAverage c
    (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc)
  let reg : Nat -> Real :=
    sixVertexCanonicalDensityPerronEmpiricalObservable hc
      (sixVertexRegularizedBetheLogKernel c (eta ^ 2))
  let I : Real := ∫ y in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogKernel c (eta ^ 2) y *
      sixVertexFourierPhysicalDensity c hc y
  let upper : Nat -> Real :=
    sixVertexCanonicalRegularizationUpper c (eta ^ 2) eta
  let E : Real := sixVertexCanonicalRegularizationDiagonalEnvelope c eta
  have hraw : Tendsto raw atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) :=
    tendsto_sixVertexCanonicalDensityPerronRootAverage hc
  have hreg : Tendsto reg atTop (nhds I) :=
    tendsto_sixVertexCanonicalDensityPerronRegularizedLogKernel hc
      (sq_pos_of_pos heta)
  have hupper : Tendsto upper atTop (nhds E) := by
    exact tendsto_sixVertexCanonicalRegularizationUpper
      (by linarith : c ≠ 0) heta
  have herror : Tendsto (fun k => raw k - reg k) atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc - I)) :=
    hraw.sub hreg
  have hnonnegEventually : ∀ᶠ k : Nat in atTop, 0 <= raw k - reg k := by
    filter_upwards [] with k
    exact (sixVertexCanonicalDensityPerronRootAverage_regularized_error_bounds
      hc (sq_pos_of_pos heta) hetaSq
      (sixVertexCanonicalLinearEdgeCutoff_pos heta k) k).1
  have hlimitNonneg : 0 <=
      sixVertexCanonicalDensityPerronRootAverageLimit hc - I :=
    ge_of_tendsto herror hnonnegEventually
  have hupperEventually : ∀ᶠ k : Nat in atTop,
      raw k - reg k <= upper k := by
    filter_upwards [] with k
    exact
      sixVertexCanonicalDensityPerronRootAverage_regularized_error_le_upper
        hc (sq_pos_of_pos heta) hetaSq heta hetaQuarter k
  have hdiffT : Tendsto (fun k => (raw k - reg k) - upper k) atTop
      (nhds ((sixVertexCanonicalDensityPerronRootAverageLimit hc - I) - E)) :=
    herror.sub hupper
  have hlimitUpper :
      sixVertexCanonicalDensityPerronRootAverageLimit hc - I <= E := by
    have hz : (sixVertexCanonicalDensityPerronRootAverageLimit hc - I) - E <=
        0 := le_of_tendsto hdiffT (by
      filter_upwards [hupperEventually] with k hk
      linarith)
    linarith
  change |sixVertexCanonicalDensityPerronRootAverageLimit hc - I| <= E
  rw [abs_of_nonneg hlimitNonneg]
  exact hlimitUpper


theorem tendsto_sixVertexCentralWidthRate_canonicalDensityPerronLimit
    {c : Real} (hc : 2 < c) :
    Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexCanonicalDensityPerronRootAverageLimit hc)) := by
  have hlog : Tendsto (fun k : Nat =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real)) atTop (nhds 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat
      (Real.log 2 / 4)).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext k
    simp [sixVertexFourWidth]
    field_simp
  have hroot := tendsto_sixVertexCanonicalDensityPerronRootAverage hc
  have hsum := hlog.add hroot
  have heq : sixVertexCentralWidthRate c =ᶠ[atTop] fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalDensityPerronPositiveHalfRootFamily hc) k := by
    filter_upwards
    [eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc]
      with k hk
    unfold sixVertexCentralWidthRate
    rw [hk, sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
    unfold sixVertexSymmetricBetheRootAverage
      sixVertexCanonicalDensityPerronPositiveHalfRootFamily
    ring
  simpa only [zero_add] using hsum.congr' heq.symm

end
end StatMech.FrontierD
