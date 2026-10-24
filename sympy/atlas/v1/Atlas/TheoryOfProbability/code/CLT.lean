/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/CLT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CentralLimitTheorem

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

/-- Density of the standard normal distribution `N(0,1)`:
`φ(x) = (2π)^{-1/2} exp(-x²/2)`. -/
def stdGaussianDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The standard normal probability measure on `ℝ`, defined as Lebesgue measure
weighted by the standard Gaussian density `stdGaussianDensity`. -/
def stdNormalMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (stdGaussianDensity x))

/-- A sequence of real random variables `Xₙ : Ω → ℝ` on a measure space `(Ω, P)`
**converges in distribution** to a measure `ν` on `ℝ` if for every bounded
continuous `f : ℝ → ℝ`, `E[f(Xₙ)] → ∫ f dν` (the Portmanteau characterization
of weak convergence). -/
def ConvergesInDistributionRV
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) (ν : Measure ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun n => ∫ x, f x ∂(P.map (X n))) atTop (𝓝 (∫ x, f x ∂ν))
