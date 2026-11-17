/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensionalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
public section

open Filter Finset Topology


namespace StatMech.FrontierA

structure PositiveAdditiveOperator (X : Type*) where
  toFun : (X → ℝ) → X → ℝ
  monotone : Monotone toFun
  map_zero : toFun 0 = 0
  map_add : ∀ f g, toFun (f + g) = toFun f + toFun g

end StatMech.FrontierA
