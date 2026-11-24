module
public import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter3.Setup
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter2.Thm_2_2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
set_option maxHeartbeats 4800000
open Matrix MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter3/Thm_3_3.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace Rigollet.Chapter3

/-- Empirical mean squared error: `MSE'(fhat, f) = (1/n) ∑ᵢ (fhatᵢ - fᵢ)²`. -/
noncomputable def MSE' {n : ℕ} (fhat f : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, (fhat i - f i) ^ 2

end Rigollet.Chapter3
