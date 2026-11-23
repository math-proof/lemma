/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_16

@[expose] public section

set_option maxHeartbeats 800000

open Matrix Finset BigOperators MeasureTheory ProbabilityTheory Real ENNReal


/-- Map `Fin 2 → ℝ` sending the bit `0` to `-1` and `1` to `+1`; converts a coin flip
into a Rademacher sign. -/
def coinToSign : Fin 2 → ℝ := fun b => if b = 0 then -1 else 1

