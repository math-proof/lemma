/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Remark_5_17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
open Finset BigOperators Real


noncomputable section

namespace Rigollet.Chapter5

/-- Sparse hypothesis vector indexed by a binary mask `ω`: places mass `R/k`
on coordinates with `ω i = true` and `0` elsewhere. -/
def sparseVec {d : ℕ} (ω : Fin d → Bool) (R : ℝ) (k : ℝ) : Fin d → ℝ :=
  fun i => if ω i then R / k else 0

end Rigollet.Chapter5
end
