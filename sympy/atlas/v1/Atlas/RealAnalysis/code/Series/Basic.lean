/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Real_Analysis.Series

/-- A real series `∑ x n` is absolutely convergent if the series of absolute values
`∑ |x n|` is summable. -/
def AbsolutelyConvergent (x : ℕ → ℝ) : Prop := Summable (fun n => |x n|)

/-- The series `∑ x n` converges if the sequence of partial sums
`s m = ∑ n ∈ range m, x n` converges to some real number `s`. -/
def SeriesConverges (x : ℕ → ℝ) : Prop :=
  ∃ s, Tendsto (fun m => ∑ n ∈ range m, x n) atTop (nhds s)

end Real_Analysis.Series
