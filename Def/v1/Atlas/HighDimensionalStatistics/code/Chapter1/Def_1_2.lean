/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Def_1_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open MeasureTheory Real


/-- **Definition 1.2 (Sub-Gaussian random variable).** A real-valued random
variable `X` on `(Ω, μ)` is sub-Gaussian with variance proxy `σ²` if it is
integrable with `E[X] = 0`, has finite MGF everywhere, and satisfies the
Gaussian-style MGF bound `E[exp(sX)] ≤ exp(σ² s² / 2)` for every `s ∈ ℝ`.
This is the notation `X ~ subG(σ²)` from the textbook. -/
def IsSubGaussian {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (σsq : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  Integrable X μ ∧
  ∫ ω, X ω ∂μ = 0 ∧
  (∀ s : ℝ, Integrable (fun ω => Real.exp (s * X ω)) μ) ∧
  ∀ s : ℝ, ∫ ω, Real.exp (s * X ω) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)

