/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
open Filter Finset Topology


namespace StatMech.FrontierA

structure PositiveAdditiveOperator (X : Type*) where
  toFun : (X → ℝ) → X → ℝ
  monotone : Monotone toFun
  map_zero : toFun 0 = 0
  map_add : ∀ f g, toFun (f + g) = toFun f + toFun g

end StatMech.FrontierA
