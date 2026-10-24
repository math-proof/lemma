/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Fourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Integration

open MeasureTheory Real Filter Set intervalIntegral Topology

/-- The `n`-th cosine Fourier coefficient of a function `f : ℝ → ℝ`, defined as
`(1/π) ∫_{-π}^{π} f(x) · cos(n·x) dx`. This corresponds to the coefficient `bₙ`
in the Fourier series expansion of `f`. -/
noncomputable def fourierCoefficientCos (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  (1 / Real.pi) * ∫ x in (-Real.pi)..Real.pi, f x * Real.cos (n * x)
