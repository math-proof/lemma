/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Lemma_3_13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace Chapter3

open Finset BigOperators

/-- The trigonometric design matrix `Φ ∈ ℝ^{n × M}` for the regular grid `X_i = (i-1)/n`
with the standard trigonometric basis: column `0` is the constant `1`, odd columns
correspond to `√2 · cos(2π k X_i)`, and even columns to `√2 · sin(2π k X_i)`. -/
noncomputable def trigDesignMatrix (n M : ℕ) : Matrix (Fin n) (Fin M) ℝ :=
  fun i j =>
    if j.val = 0 then 1
    else if j.val % 2 = 1 then
      Real.sqrt 2 * Real.cos (2 * Real.pi * (↑((j.val + 1) / 2) : ℝ) * ↑(i : ℕ) / ↑n)
    else
      Real.sqrt 2 * Real.sin (2 * Real.pi * (↑(j.val / 2) : ℝ) * ↑(i : ℕ) / ↑n)

end Chapter3
