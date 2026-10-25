/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangHalfPlaneDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.HolomorphicFamilyEquicontinuity
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangRealAnchor.Part5
import Def.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part3
open Filter Metric Set Topology
open scoped UniformConvergence


namespace StatMech.FrontierA

open StatMech.FK


theorem leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | 0 < z.re} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  have hdata :=
    leeYangBox_normalizedFieldLogDerivative_normalFamilyData_rightHalfPlane d hbeta
  exact holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    F {z : ℂ | 0 < z.re}
    (isOpen_lt continuous_const Complex.continuous_re)
    hdata.1 hdata.2 rightHalfPlaneCompactExhaustion


theorem leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane
    (d : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    IsLocallyUniformlySequentiallyPrecompact
      (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
      {z : ℂ | z.re < 0} := by
  let F : ℕ → ℂ → ℂ := fun n =>
    leeYangNormalizedFieldLogDerivative (boxGraph d n) beta
  have hdata :=
    leeYangBox_normalizedFieldLogDerivative_normalFamilyData_leftHalfPlane d hbeta
  exact holomorphicFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    F {z : ℂ | z.re < 0}
    (isOpen_lt Complex.continuous_re continuous_const)
    hdata.1 hdata.2 leftHalfPlaneCompactExhaustion


theorem leeYangBox_normalizedFieldLogDerivative_rightHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | 0 < z.re} ∧
      DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | 0 < z.re} :=
  leeYangBox_normalizedFieldLogDerivative_rightHalfPlane_of_precompact
    d hd hbeta
    (leeYangBox_normalizedFieldLogDerivative_precompact_rightHalfPlane d hbeta)


theorem leeYangBox_normalizedFieldLogDerivative_leftHalfPlane
    (d : ℕ) (hd : 1 ≤ d) {beta : ℝ} (hbeta : 0 < beta) :
    ∃ g : ℂ → ℂ,
      TendstoLocallyUniformlyOn
        (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        g atTop {z : ℂ | z.re < 0} ∧
      DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧
      TendstoLocallyUniformlyOn
        (deriv ∘ fun n =>
          leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        (deriv g) atTop {z : ℂ | z.re < 0} :=
  leeYangBox_normalizedFieldLogDerivative_leftHalfPlane_of_precompact
    d hd hbeta
    (leeYangBox_normalizedFieldLogDerivative_precompact_leftHalfPlane d hbeta)

end StatMech.FrontierA
