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
public import Structure.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction

@[expose] public section

open Filter Finset Topology


namespace StatMech.FrontierA

instance {X : Type*} : CoeFun (PositiveAdditiveOperator X)
    (fun _ => (X → ℝ) → X → ℝ) :=
  ⟨PositiveAdditiveOperator.toFun⟩


end StatMech.FrontierA
