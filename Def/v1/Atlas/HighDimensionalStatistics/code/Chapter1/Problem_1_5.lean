/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Independence.Basic
open MeasureTheory ProbabilityTheory Real Finset


noncomputable section

/-- The ℓq (quasi)norm on `Fin n → ℝ`:
`‖x‖_q = (∑ |xᵢ|^q)^{1/q}`. -/
noncomputable def lqNorm (n : ℕ) (q : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |x i| ^ q) ^ (1 / q)

end
