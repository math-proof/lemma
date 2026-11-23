/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Independence.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset


noncomputable section

/-- The ℓq (quasi)norm on `Fin n → ℝ`:
`‖x‖_q = (∑ |xᵢ|^q)^{1/q}`. -/
noncomputable def lqNorm (n : ℕ) (q : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |x i| ^ q) ^ (1 / q)

end
