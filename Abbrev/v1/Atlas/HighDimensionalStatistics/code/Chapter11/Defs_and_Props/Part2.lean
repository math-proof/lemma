/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part2
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

section Def_11_8

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [(MeasureTheory.volume : Measure E).HasTemperateGrowth]

/-- Textbook alias for `IsParametrix` (Definition 11.8, parametrix part). -/
abbrev def_11_8_parametrix := @IsParametrix

/-- Textbook alias for `IsHypoelliptic` (Definition 11.8, hypoelliptic part). -/
abbrev def_11_8_hypoelliptic := @IsHypoelliptic

end Def_11_8
end Chapter11
end
