/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_16
set_option maxHeartbeats 800000

open Matrix Finset BigOperators MeasureTheory ProbabilityTheory Real ENNReal


/-- The fair coin distribution is a probability measure. -/
instance coinMeasure_prob : IsProbabilityMeasure coinMeasure := by
  refine ⟨?_⟩
  simp [coinMeasure, Measure.add_apply, Measure.smul_apply]
  simp only [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

