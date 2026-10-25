/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part3
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

/-- Textbook alias for `IsElliptic` (Definition 11.11). -/
abbrev def_11_11_elliptic := @IsElliptic

end Chapter11
end
