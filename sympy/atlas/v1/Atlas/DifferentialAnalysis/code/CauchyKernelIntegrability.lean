/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CauchyKernelIntegrability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
open Real Set MeasureTheory Metric
open scoped ENNReal Real Topology

namespace CauchyKernel

noncomputable section

/-- The Cauchy kernel `K(x, y) = (2π)^{-1} · (x + i y)^{-1}` on `ℝ²`,
identifying a real point `(x, y)` with the complex number `x + i y`.
Acts as a fundamental solution for the Cauchy–Riemann operator. -/
def cauchyKernel (p : ℝ × ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ((↑p.1 + Complex.I * ↑p.2) : ℂ)⁻¹

/-- The Cauchy kernel without the `(2π)^{-1}` prefactor: `(x + i y)^{-1}`.
Useful for integrability arguments where the constant is irrelevant. -/
def cauchyKernelBare (p : ℝ × ℝ) : ℂ :=
  ((↑p.1 + Complex.I * ↑p.2) : ℂ)⁻¹
