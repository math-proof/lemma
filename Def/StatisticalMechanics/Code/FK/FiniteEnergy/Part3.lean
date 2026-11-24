module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.Comparison
public import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part3
open scoped BigOperators
open Module SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cFE (p q : ℝ) : ℝ := min (p / (p + q * (1 - p))) (1 - p)


end FK
end StatMech
