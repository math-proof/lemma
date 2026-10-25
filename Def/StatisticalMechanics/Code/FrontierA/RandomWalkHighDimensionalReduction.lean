/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Instance.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction
open Filter Finset Topology


namespace StatMech.FrontierA

def randomWalkIterate {X : Type*} (T : PositiveAdditiveOperator X) :
    ℕ → (X → ℝ) → X → ℝ
  | 0, f => f
  | n + 1, f => T (randomWalkIterate T n f)

end StatMech.FrontierA
