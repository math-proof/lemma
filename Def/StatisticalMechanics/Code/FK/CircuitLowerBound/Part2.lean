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
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def agreeWeightSum (p q : ℝ) (γ : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : ConfigSpace (Sym2 V) => ∀ e' ∉ γ, σ e' = ψ e'),
    fkWeight G p q σ


end FK
end StatMech
