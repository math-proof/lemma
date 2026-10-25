/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Def.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction
open Filter Finset Topology


namespace StatMech.FrontierA

@[simp] theorem randomWalkIterate_zero {X : Type*}
    (T : PositiveAdditiveOperator X) (f : X → ℝ) :
    randomWalkIterate T 0 f = f := rfl

@[simp] theorem randomWalkIterate_succ {X : Type*}
    (T : PositiveAdditiveOperator X) (n : ℕ) (f : X → ℝ) :
    randomWalkIterate T (n + 1) f = T (randomWalkIterate T n f) := rfl


end StatMech.FrontierA
