/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter10/Schwartz_Repr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter10.Schwartz_Repr
set_option maxHeartbeats 200000

open scoped SchwartzMap
open MeasureTheory LineDeriv


noncomputable section

/-- Decidability instance for the componentwise order on multi-indices. -/
instance MultiIndex.decidableLe {n : ℕ} (α γ : MultiIndex n) :
    Decidable (MultiIndex.le α γ) :=
  Fintype.decidableForallFintype

end
