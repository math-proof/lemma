/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
public import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1

@[expose] public section

open MeasureTheory Matrix Real Finset


noncomputable section

/-- The observed matrix in the sub-Gaussian model: `y = Θstar + F(ω)`. -/
def SubGaussianMatrixModel.observed {Ω : Type*} [MeasurableSpace Ω]
    {d T : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (model : SubGaussianMatrixModel Ω d T μ) (ω : Ω) : Matrix (Fin d) (Fin T) ℝ :=
  model.Θstar + model.F ω

end
