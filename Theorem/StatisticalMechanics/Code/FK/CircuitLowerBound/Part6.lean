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
import Def.StatisticalMechanics.Code.FK.CircuitLowerBound.Part5
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem closedMass_eq_indicator_sum (p q : ℝ) (γ : Finset (Sym2 V)) :
    closedMass G p q γ
      = ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
  classical
  unfold closedMass
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases hω : ∀ e ∈ γ, ω e = false
  · have hmem : ω ∈ closedEvent γ := hω
    rw [if_pos hω, Set.indicator_of_mem hmem, one_mul]
  · have hnmem : ω ∉ closedEvent γ := hω
    rw [if_neg hω, Set.indicator_of_notMem hnmem, zero_mul]


theorem cFE_pow_le_closedEventMass {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (γ : Finset (Sym2 V)) :
    cFE p q ^ γ.card
      ≤ ∑ ω, (closedEvent γ).indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω := by
  rw [← closedMass_eq_indicator_sum]
  exact cFE_pow_le_closedMass G hp hp1 hq γ

end FK
end StatMech
