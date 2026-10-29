/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Def.StatisticalMechanics.Code.Inequalities.ReimerClose2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace

variable {E : Type*}


theorem reimer_wprob_of_negCorr [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) {A B : Set (ConfigSpace E)} (h : NegativelyCorrelated φ A B) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B :=
  le_trans (wprob_disjointOccurrence_le_inter hφ0 A B) h


theorem reimer_wprob_of_inter_empty [Fintype E] [DecidableEq E] {φ : E → Bool → ℝ}
    (hφ0 : ∀ x b, 0 ≤ φ x b) {A B : Set (ConfigSpace E)} (h : A ∩ B = ∅) :
    wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
  refine reimer_wprob_of_negCorr hφ0 ?_
  unfold NegativelyCorrelated
  rw [h]
  have hempty : wprob φ (∅ : Set (ConfigSpace E)) = 0 := by unfold wprob; simp
  rw [hempty]
  exact mul_nonneg (wprob_nonneg hφ0 A) (wprob_nonneg hφ0 B)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem reimer_inequality_of_inter_empty [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1)
    {A B : Set (ConfigSpace E)} (h : A ∩ B = ∅) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  set φ : E → Bool → ℝ := fun (_ : E) (b : Bool) => (bernoulliMeasure p hp).real {b} with hφ
  have hφ0 : ∀ x b, 0 ≤ φ x b := fun _ _ => measureReal_nonneg
  rw [bernoulli_real_eq_wprob hp (disjointOccurrence A B), bernoulli_real_eq_wprob hp A,
    bernoulli_real_eq_wprob hp B]
  exact reimer_wprob_of_inter_empty hφ0 h


end StatMech
