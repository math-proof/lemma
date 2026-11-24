module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
public import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def closeAllOn (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 V) := fun e => if e ∈ γ then false else ψ e

end FK
end StatMech
