/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Problem_3_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory Real Set


noncomputable section

/-- Trigonometric basis on `[0,1]` defined by recursion: `φ₀ = 0`, `φ₁ = 1`,
and for `j ≥ 2`, `φⱼ` is either `√2 cos(2π k x)` or `√2 sin(2π k x)`
depending on the parity of `j`. -/
def trigBasis : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun _ => 1
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      fun x => √2 * cos (2 * π * ((n + 2) / 2 : ℕ) * x)
    else
      fun x => √2 * sin (2 * π * ((n + 1) / 2 : ℕ) * x)

/-- Haar mother wavelet `ψ` on `[0,1]`: equals `1` on `[0, 1/2)`, `-1` on
`[1/2, 1)`, and zero elsewhere. -/
def haarMother (x : ℝ) : ℝ :=
  if x ∈ Ico (0 : ℝ) (1 / 2) then 1
  else if x ∈ Ico (1 / 2 : ℝ) 1 then -1
  else 0

/-- Haar system element `ψ_{j,k}(x) = 2^{j/2} ψ(2^j x - k)`. -/
def haarSystem (j k : ℤ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((j : ℝ) / 2) * haarMother ((2 : ℝ) ^ (j : ℝ) * x - ↑k)

end
