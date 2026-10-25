/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter10/Schwartz_Repr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter10.Schwartz_Repr
set_option maxHeartbeats 200000

open scoped SchwartzMap
open MeasureTheory LineDeriv


noncomputable section

/-- The order `|α| = α₁ + … + αₙ` of a multi-index. -/
def MultiIndex.order {n : ℕ} (α : MultiIndex n) : ℕ := ∑ i, α i

/-- Componentwise order on multi-indices: `α ≤ γ` iff `αᵢ ≤ γᵢ` for all `i`. -/
def MultiIndex.le {n : ℕ} (α γ : MultiIndex n) : Prop := ∀ i, α i ≤ γ i

end
