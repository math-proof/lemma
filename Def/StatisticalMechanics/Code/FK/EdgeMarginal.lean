module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FKG
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DensityBounds
open scoped BigOperators
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def edgeMargProb (μ : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∑ ω : ConfigSpace E, (if ω e then (1 : ℝ) else 0) * μ ω


noncomputable def eventMassProb (μ : ConfigSpace E → ℝ) (A : Set (ConfigSpace E)) : ℝ :=
  ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω * μ ω


end FK
end StatMech
