/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter12/MicrolocalAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter12.MicrolocalAnalysis.Part2
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Pointwise

open MeasureTheory Set Filter

variable {n : ℕ}

namespace Chapter12

/-- Convolution of a Schwartz function `φ` with a tempered distribution `u`,
producing a tempered distribution. Declared `opaque` to be filled in later. -/
opaque schwartzConvolution (n : ℕ) (φ : 𝓢(Rn n, ℂ)) (u : 𝓢'(Rn n, ℂ)) :
    𝓢'(Rn n, ℂ) := 0

/-- `v` is given by a conic cutoff: there is a smooth function `ψ_R` homogeneous
of degree zero outside the unit ball such that `v` integrates against it. -/
def IsConicCutoff (n : ℕ) (v : 𝓢'(Rn n, ℂ)) : Prop :=
  ∃ (ψ_R : Rn n → ℂ), ContDiff ℝ ⊤ ψ_R ∧ IsHomogeneousOutside ψ_R 0 ∧
    ∀ (f : 𝓢(Rn n, ℂ)), v f = ∫ x, f x • (ψ_R x : ℂ)

/-- The wavefront set `WF(u)`: pairs `(x, ξ)` with `ξ ≠ 0` such that, for every
compactly-supported smooth cutoff `φ` with `φ(x) ≠ 0`, the direction `ξ` lies in
the conic singular support of `φ u`. -/
def WavefrontSet (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n × Rn n) :=
  {p : Rn n × Rn n | p.2 ≠ 0 ∧
    ∀ (φ : Rn n → ℂ), ContDiff ℝ ⊤ φ → HasCompactSupport φ → φ p.1 ≠ 0 →
      p.2 ∈ ConeSingularSupport n (TemperedDistribution.smulLeftCLM ℂ φ u)}

/-- The scattering wavefront set `WF_sc(u)`: the usual wavefront set together
with pairs `(x, ξ)` of nonzero `x, ξ` such that every conic-cutoff `ψ` with
`ψ(x) ≠ 0` places `ξ` in the conic singular support of `ψ u`. -/
def ScatteringWavefrontSet (n : ℕ) (u : 𝓢'(Rn n, ℂ)) : Set (Rn n × Rn n) :=
  WavefrontSet n u ∪
    {p : Rn n × Rn n | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      ∀ (ψ : Rn n → ℂ), ContDiff ℝ ⊤ ψ → IsHomogeneousOutside ψ 0 → ψ p.1 ≠ 0 →
        p.2 ∈ ConeSingularSupport n (TemperedDistribution.smulLeftCLM ℂ ψ u)}

end Chapter12
end
