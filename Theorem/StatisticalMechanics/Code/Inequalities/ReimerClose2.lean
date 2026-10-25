/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


lemma wprob_nonneg [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ} (hφ0 : ∀ x b, 0 ≤ φ x b)
    (S : Set (ConfigSpace E)) : 0 ≤ wprob φ S := by
  unfold wprob
  refine Finset.sum_nonneg (fun ω _ => ?_)
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) (pweight_nonneg hφ0 ω)


theorem wprob_disjointOccurrence_le_inter [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) (A B : Set (ConfigSpace E)) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ (A ∩ B) :=
  wprob_mono hφ0 (disjointOccurrence_subset_inter A B)


end StatMech
