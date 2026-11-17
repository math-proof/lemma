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
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1
open MeasureTheory Matrix Real Finset


public noncomputable section

/-- A sub-Gaussian matrix observation model: an unknown signal `Θstar` is observed with
additive sub-Gaussian noise `F` having proxy variance `σsq`. -/
structure SubGaussianMatrixModel (Ω : Type*) [MeasurableSpace Ω]
    (d T : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] where
  Θstar : Matrix (Fin d) (Fin T) ℝ
  F : Ω → Matrix (Fin d) (Fin T) ℝ
  σsq : ℝ
  hF : IsSubGaussianMatrix F σsq μ

end
