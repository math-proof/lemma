/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators


namespace ProjectionTheory

/-- The finite range of dyadic exponents `{0, 1, …, ⌊log₂ R⌋}` used to index the scales
`r = 2^k` in dyadic decompositions up to a real cutoff `R`. -/
noncomputable def dyadicExponentRange (R : ℝ) : Finset ℕ :=
  Finset.range (Nat.log 2 ⌊R⌋₊ + 1)

end ProjectionTheory
