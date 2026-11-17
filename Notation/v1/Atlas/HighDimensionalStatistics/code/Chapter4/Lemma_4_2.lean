/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Lemma_4_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1.Part3
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Lemma_1_18
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

public section

open MeasureTheory Matrix Real Finset ENNReal


noncomputable section

local notation "⟪" x ", " y "⟫ᵣ" => @inner ℝ _ _ x y

end
