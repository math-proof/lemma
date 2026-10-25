/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ProjectionSmoothing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

open MeasureTheory MeasureTheory.Measure Metric Set Function Filter

namespace ProjectionSmoothing

/-- The projection `π_θ f : ℝ → ℂ` of an `L²` function `f : ℝ^d → ℂ` along the
direction `θ ∈ S^{d−1}`: at the point `t ∈ ℝ` it returns the integral of `f` over
the affine hyperplane `t·θ + θ^⊥`, with respect to the Haar measure on `θ^⊥`. -/
def projectionAlongDirection {d : ℕ}
    (θ : ↥(sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (f : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ → ℂ := fun t =>
  ∫ z : ↥(Submodule.orthogonal (Submodule.span ℝ {(θ : EuclideanSpace ℝ (Fin d))})),
    f (t • (θ : EuclideanSpace ℝ (Fin d)) + (z : EuclideanSpace ℝ (Fin d)))
    ∂Measure.addHaar

/-- The `C^k` norm of a function `g : ℝ → ℂ`: the supremum over `0 ≤ j ≤ k` and
`t ∈ ℝ` of `‖g^(j)(t)‖`. -/
def ckNorm (k : ℕ) (g : ℝ → ℂ) : ℝ :=
  ⨆ (j : Fin (k + 1)), ⨆ (t : ℝ), ‖iteratedDeriv (j : ℕ) g t‖

/-- The inhomogeneous Sobolev `H^s` squared norm `∫ (1 + |ξ|²)^s |ĝ(ξ)|² dξ`
of a function `g : ℝ → ℂ`. -/
def sobolevNormSq (s : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, (1 + ‖ξ‖ ^ 2) ^ s * ‖FourierTransform.fourier g ξ‖ ^ 2

/-- **Sobolev embedding (one dimension).** If `s > 1/2 + k`, then the Sobolev
`H^s` norm controls the `C^k` norm: there is a constant `C > 0` such that
`‖g‖_{C^k}² ≤ C · ‖g‖_{H^s}²` for every `g : ℝ → ℂ`. -/
def homoSobolevNormSq (s : ℝ) (g : ℝ → ℂ) : ℝ :=
  ∫ ξ : ℝ, ‖ξ‖ ^ (2 * s) * ‖FourierTransform.fourier g ξ‖ ^ 2

end ProjectionSmoothing
end
