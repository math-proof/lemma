/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/StrassenFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StrassenFull.Part7
import Def.StatisticalMechanics.Code.Probability.StrassenFinite
open Finset
open scoped NNReal


namespace StatMech

namespace Probability

variable {P : Type*}


section Easy

variable [Fintype P] [PartialOrder P] [DecidableEq P]
  [DecidableRel ((· ≤ ·) : P → P → Prop)]

omit [DecidableEq P] in


theorem StochasticDom.of_isMonotoneCoupling {μ ν : P → ℝ≥0} {π : P × P → ℝ≥0}
    (h : IsMonotoneCoupling μ ν π) : StochasticDom μ ν := by
  intro U hU
  have hμU : ∑ x ∈ U, μ x = ∑ p ∈ U ×ˢ (univ : Finset P), π p := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun x _ => (h.fst_marginal x).symm)
  have hνU : ∑ y ∈ U, ν y = ∑ p ∈ (univ : Finset P) ×ˢ U, π p := by
    rw [Finset.sum_product, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => (h.snd_marginal y).symm)
  rw [hμU, hνU]
  
  have hLHS : ∑ p ∈ U ×ˢ (univ : Finset P), π p
      = ∑ p ∈ (U ×ˢ (univ : Finset P)).filter (fun p => p.1 ≤ p.2), π p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hp : p.1 ≤ p.2
    · rw [if_pos hp]
    · rw [if_neg hp]; exact h.supported p.1 p.2 hp
  rw [hLHS]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hU hp.2 hp.1
  · intro p _ _; exact zero_le'

end Easy
end Probability
end StatMech
