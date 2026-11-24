module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_6
public import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Thm_4_6
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter4.Cor_4_9
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Cor_4_9
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/EuclideanBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

set_option linter.unusedVariables false

set_option maxHeartbeats 800000

variable {d : ℕ}

namespace EuclideanBridge

/-- Forget the Euclidean (`L²`) structure, viewing a vector as a plain function `Fin d → ℝ`. -/
def euclideanToFun : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ) := WithLp.equiv 2 (Fin d → ℝ)

/-- Equip a plain function `Fin d → ℝ` with the Euclidean (`L²`) structure. -/
def funToEuclidean : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm

end EuclideanBridge
end
