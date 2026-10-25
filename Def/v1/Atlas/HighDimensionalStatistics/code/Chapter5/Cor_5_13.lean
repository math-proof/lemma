/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.ExponentialBounds
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_3_5_4_5_8
open MeasureTheory InformationTheory


noncomputable section

namespace GaussianSequenceModel

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- An estimator is a function mapping observations in `ℝ^d` to a parameter estimate in `ℝ^d`. -/
def Estimator (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

end GaussianSequenceModel
end
