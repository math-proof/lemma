/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Ex_3_9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory Set intervalIntegral Filter


noncomputable section

namespace Chapter3

/-- Haar mother wavelet on `[0,1]`: equals `1` on `[0, 1/2)`, `-1` on
`[1/2, 1]`, and zero elsewhere. -/
def haarMother (x : ℝ) : ℝ :=
  if 0 ≤ x ∧ x < 1 / 2 then 1
  else if 1 / 2 ≤ x ∧ x ≤ 1 then -1
  else 0

/-- Haar wavelet at scale `j` and translation `k`:
`ψ_{j,k}(x) = 2^{j/2} ψ(2^j x - k)` where `ψ` is the Haar mother wavelet. -/
def haarWavelet (j k : ℤ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2) * haarMother ((2 : ℝ) ^ (j : ℤ) * x - ↑k)

/-- Wavelet coefficient of `g` at scale `j` and translation `k`:
`∫₀¹ g(x) ψ_{j,k}(x) dx`. -/
def waveletCoeff (g : ℝ → ℝ) (j k : ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..1, g x * haarWavelet j k x

end Chapter3
end
