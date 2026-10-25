/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter12/MicrolocalAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter12.MicrolocalAnalysis.Part3
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Pointwise

open MeasureTheory Set Filter

variable {n : ℕ}

namespace Chapter12

/-- The singular support of a tempered distribution on `ℝⁿ`. -/
def SingularSupport (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n) :=
  {x : Rn n |
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ x ≠ 0 →
      TemperedDistribution.smulLeftCLM ℂ φ u ∉
        Set.range (SchwartzMap.toTemperedDistributionCLM (Rn n) ℂ)}

/-- Product of two tempered distributions, defined when their wavefront sets
satisfy Hörmander's compatibility condition. Declared `opaque` for later use. -/
opaque distribProduct (n : ℕ) (u v : 𝓢'(Rn n, ℂ))
    (h : ∀ p q : Rn n × Rn n,
      p ∈ WavefrontSet n u → q ∈ WavefrontSet n v → p.1 = q.1 → p.2 + q.2 ≠ 0) :
    𝓢'(Rn n, ℂ) := 0

/-- The closed unit ball in `ℝⁿ`. -/
def closedUnitBall (n : ℕ) : Set (Rn n) := Metric.closedBall 0 1

/-- The unit sphere in `ℝⁿ`. -/
def unitSphere (n : ℕ) : Set (Rn n) := Metric.sphere 0 1

/-- Compatibility condition between `WF_sc(u)` and `WF_sc(v)` required for the
product distribution `u · v` to be defined in the scattering calculus. -/
def ProductWFscCondition (n : ℕ) (u v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∀ (p ω : Rn n),
    (p, ω) ∈ ScatteringWavefrontSet n u →
    p ∈ closedUnitBall n →
    ω ∈ unitSphere n →
    (p, -ω) ∉ ScatteringWavefrontSet n v

/-- Compatibility condition between `WF_sc(u)` and `WF_sc(v)` required for the
convolution `u * v` to be defined in the scattering calculus. -/
def ConvolutionWFscCondition (n : ℕ) (u v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∀ (θ q : Rn n),
    (θ, q) ∈ ScatteringWavefrontSet n u →
    θ ∈ unitSphere n →
    q ∈ closedUnitBall n →
    (-θ, q) ∉ ScatteringWavefrontSet n v

/-- Product of distributions in the scattering calculus, defined under the
appropriate compatibility on their scattering wavefront sets. -/
opaque distribProductSc (n : ℕ) (u v : 𝓢'(Rn n, ℂ))
    (h : ProductWFscCondition n u v) : 𝓢'(Rn n, ℂ) := 0

/-- Convolution of distributions in the scattering calculus, defined under the
appropriate compatibility on their scattering wavefront sets. -/
opaque distribConvolutionSc (n : ℕ) (u v : 𝓢'(Rn n, ℂ))
    (h : ConvolutionWFscCondition n u v) : 𝓢'(Rn n, ℂ) := 0

end Chapter12
end
