/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Walls.rc17arbitrary
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc17_deficitBridge_of_nonMonotone (h : rc17_NonMonotoneDeficit) : rc7_DeficitBridge := by
  intro n A B
  by_cases hAi : IsIncreasing A
  · by_cases hBi : IsIncreasing B
    · exact rc17_deficit_le_zero_of_bothMonotone (Or.inl hAi) (Or.inl hBi)
    · by_cases hBd : IsDecreasing B
      · exact rc17_deficit_le_zero_of_bothMonotone (Or.inl hAi) (Or.inr hBd)
      · exact h n A B (Or.inr ⟨hBi, hBd⟩)
  · by_cases hAd : IsDecreasing A
    · by_cases hBi : IsIncreasing B
      · exact rc17_deficit_le_zero_of_bothMonotone (Or.inr hAd) (Or.inl hBi)
      · by_cases hBd : IsDecreasing B
        · exact rc17_deficit_le_zero_of_bothMonotone (Or.inr hAd) (Or.inr hBd)
        · exact h n A B (Or.inr ⟨hBi, hBd⟩)
    · exact h n A B (Or.inl ⟨hAi, hAd⟩)


theorem rc17_nonMonotone_of_deficitBridge (h : rc7_DeficitBridge) : rc17_NonMonotoneDeficit :=
  fun n A B _ => h n A B


theorem rc17_deficitBridge_iff_nonMonotone : rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit :=
  ⟨rc17_nonMonotone_of_deficitBridge, rc17_deficitBridge_of_nonMonotone⟩


theorem rc17_reimerCardFormAll_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerCardFormAll :=
  rc7_reimerCardFormAll_of_deficitBridge (rc17_deficitBridge_of_nonMonotone h)


theorem rc17_reimerResidue_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerResidue :=
  rc7_reimerCardFormAll_iff_residue.mp (rc17_reimerCardFormAll_of_nonMonotone h)


theorem rc17_reimerWprobCore_of_nonMonotone (h : rc17_NonMonotoneDeficit) : ReimerWprobCore :=
  rc3_core_reimerWprobCore_of_residue (rc17_reimerResidue_of_nonMonotone h)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in


theorem rc17_reimer_inequality_of_nonMonotone (h : rc17_NonMonotoneDeficit) {E : Type*}
    [Fintype E] [DecidableEq E] {p : ℝ≥0} (hp : p ≤ 1) (A B : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B)
      ≤ (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B :=
  reimer_inequality_of_core (rc17_reimerWprobCore_of_nonMonotone h) hp A B


end StatMech.Walls
