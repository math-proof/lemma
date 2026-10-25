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
import Def.StatisticalMechanics.Code.FK.CircuitLowerBound.Part3
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem closedMass_empty {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    closedMass G p q ∅ = 1 := by
  classical
  unfold closedMass
  rw [show (Finset.univ.filter
      (fun ω : ConfigSpace (Sym2 V) => ∀ e ∈ (∅ : Finset (Sym2 V)), ω e = false))
      = Finset.univ from by ext ω; simp]
  exact fkProb_sum_eq_one G hp hp1 hq


end FK
end StatMech
