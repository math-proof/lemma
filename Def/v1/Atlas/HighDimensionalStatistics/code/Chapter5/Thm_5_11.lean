/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Thm_5_11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
open MeasureTheory InformationTheory Real Finset


noncomputable section

namespace MinimaxLowerBound

/-- Squared Euclidean distance `∑ i, (θ₁ i - θ₂ i)²` on `Fin d → ℝ`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- An estimator in dimension `d` is a map `ℝ^d → ℝ^d` from observations to
parameter estimates. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

end MinimaxLowerBound
end
