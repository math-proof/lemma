/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.FourierAnalysis.code.FourierSeries
open MeasureTheory MeasureTheory.Measure AddCircle
open scoped ENNReal NNReal Convolution

open MeasureTheory Filter Topology Set intervalIntegral Real


noncomputable section

namespace ApproximateIdentity

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

end ApproximateIdentity

end

open ContinuousMap Set

namespace TrigPolyDensity

end TrigPolyDensity

open MeasureTheory Filter Topology Set intervalIntegral Real

noncomputable section

namespace FejerL1Density

def periodicL1Norm (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-π)..π, |f x|

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

def fejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  if N = 0 then 0
  else if sin (x / 2) = 0 then (N : ℝ)
  else (1 / N : ℝ) * (sin (N * x / 2) / sin (x / 2)) ^ 2

def fejerMean (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  periodicConvolution f (fejerKernel N)

def IsTrigPolynomial (p : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (a b : ℕ → ℝ),
    ∀ x, p x = ∑ n ∈ Finset.range (N + 1),
      (a n * cos (n * x) + b n * sin (n * x))

end FejerL1Density
end
