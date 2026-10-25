/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part4
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def cfib (e : Sym2 V) (γ : Finset (Sym2 V)) :
    Finset (ConfigSpace (Sym2 V)) :=
  Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false ∧ ∀ e' ∈ γ, ψ e' = false)


end FK
end StatMech
