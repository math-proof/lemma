/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Chapter3

open MeasureTheory

/-- Trigonometric basis on `[0,1]`: `φ₁ = 1`, and for `j ≥ 2`,
`φ_{2k}(x) = √2 cos(2π k x)`, `φ_{2k+1}(x) = √2 sin(2π k x)`. -/
noncomputable def trigBasis (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 0
  else if j = 1 then 1
  else if j % 2 = 0 then Real.sqrt 2 * Real.cos (2 * Real.pi * (j / 2 : ℕ) * x)
  else Real.sqrt 2 * Real.sin (2 * Real.pi * ((j - 1) / 2 : ℕ) * x)

/-- The `j`-th Fourier coefficient of `f` with respect to the trigonometric
basis: `∫₀¹ f(x) φⱼ(x) dx`. -/
noncomputable def fourierCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, f x * trigBasis j x
