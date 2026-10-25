/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1.Part2
open MeasureTheory Matrix Real Finset


noncomputable section

/-- A singular value decomposition record for a `d × T` matrix: rank `r`, singular values
`σval`, and the corresponding left/right singular vectors `u`, `v`. -/
structure SVD (d T : ℕ) where
  r : ℕ
  hr : r ≤ min d T
  σval : Fin r → ℝ
  u : Fin r → (Fin d → ℝ)
  v : Fin r → (Fin T → ℝ)
  σval_nonneg : ∀ j, 0 ≤ σval j

end
