module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FKG
public import Theorem.StatisticalMechanics.Code.FK.Comparison
public import Theorem.StatisticalMechanics.Code.FK.Limits
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Inequalities.FKG
public import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
public import Theorem.StatisticalMechanics.Code.FK.MonoBC
open scoped BigOperators
open SimpleGraph
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/MonoBC.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable (bdry : V → Prop) [DecidablePred bdry]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


noncomputable def bcWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClustersBC G C ω

end FK
end StatMech
