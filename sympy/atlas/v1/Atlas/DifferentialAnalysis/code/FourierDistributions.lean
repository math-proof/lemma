/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped SchwartzMap FourierTransform
open MeasureTheory

noncomputable section

namespace FourierDistributions

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform on tempered distributions, packaged as a continuous linear
equivalence of `𝓢'(V, ℂ)` with itself. -/
def fourierTempDistribCLE : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ) :=
  FourierTransform.fourierCLE ℂ 𝓢'(V, ℂ)

/-- Iterated multiplication by linear functionals: for a tuple `m : Fin n → V`, the operator
`iteratedMulOp m` multiplies a tempered distribution by `∏ ⟨·, m i⟩`. Defined by recursion. -/
def iteratedMulOp : {n : ℕ} → (Fin n → V) → 𝓢'(V, ℂ) → 𝓢'(V, ℂ)
  | 0, _, u => u
  | _ + 1, m, u => smulLeftCLM ℂ (inner ℝ · (m 0)) (iteratedMulOp (Fin.tail m) u)
