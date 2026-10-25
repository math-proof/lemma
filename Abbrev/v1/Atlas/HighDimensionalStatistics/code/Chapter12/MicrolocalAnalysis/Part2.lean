/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter12/MicrolocalAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter12.MicrolocalAnalysis
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Pointwise

open MeasureTheory Set Filter

variable {n : ℕ}

namespace Chapter12

/-- Textbook alias for `ConeSupport` (Definition 12.2). -/
abbrev def_12_2_cone_support := @ConeSupport

/-- Textbook alias for `ConeSingularSupport` (Definition 12.2). -/
abbrev def_12_2_cone_singular_support := @ConeSingularSupport

end Chapter12
end
