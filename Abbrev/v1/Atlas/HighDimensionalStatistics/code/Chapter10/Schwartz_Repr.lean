/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter10/Schwartz_Repr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
set_option maxHeartbeats 200000

open scoped SchwartzMap
open MeasureTheory LineDeriv


noncomputable section

/-- A multi-index of dimension `n` is a tuple of natural numbers `Fin n → ℕ`. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

end
