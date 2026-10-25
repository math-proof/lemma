/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction
open Filter Finset Topology


namespace StatMech.FrontierA

def randomWalkPartial {X : Type*} (T : PositiveAdditiveOperator X)
    (delta : X → ℝ) : ℕ → X → ℝ
  | 0 => 0
  | n + 1 => delta + T (randomWalkPartial T delta n)

end StatMech.FrontierA
