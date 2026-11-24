module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
public import Theorem.StatisticalMechanics.Code.FK.DensityBounds
public import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkMeanOpenCount (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), (chOpenCount G ω : ℝ) * fkProb G p q ω


end FK
end StatMech
