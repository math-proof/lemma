/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourDynamicCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoStepCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourWeightedConvolution
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourDynamicCount.Part2
open Finset


namespace StatMech.FrontierD

theorem sixVertexFourVerticalRowsTotalC_eq_twoStepGrades
    (seam opposite middle0 middle2 : Fin 16) :
    sixVertexVerticalRowsTotalC
        (T := sixVertexFourByFourTorus) ![
          sixVertexFourRowOfIndex middle0,
          sixVertexFourRowOfIndex opposite,
          sixVertexFourRowOfIndex middle2,
          sixVertexFourRowOfIndex seam] =
      sixVertexFourTwoStepGrade seam middle0 opposite +
        sixVertexFourTwoStepGrade opposite middle2 seam := by
  unfold sixVertexVerticalRowsTotalC sixVertexFourTwoStepGrade
  let f : Fin 4 → Nat := fun j =>
    sixVertexRowDistance
      ((![sixVertexFourRowOfIndex middle0,
          sixVertexFourRowOfIndex opposite,
          sixVertexFourRowOfIndex middle2,
          sixVertexFourRowOfIndex seam] : Fin 4 → SixVertexRow 4)
        (SixVertexArrows.cyclicPred
          sixVertexFourByFourTorus.height_pos j))
      ((![sixVertexFourRowOfIndex middle0,
          sixVertexFourRowOfIndex opposite,
          sixVertexFourRowOfIndex middle2,
          sixVertexFourRowOfIndex seam] : Fin 4 → SixVertexRow 4) j)
  change (∑ j, f j) = _
  calc
    _ = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f
    _ = _ := by
      norm_num [f, SixVertexArrows.cyclicPred,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three]
      omega

theorem sixVertexFourWitnessProduct_eq_twoStepWeights
    (seam opposite middle0 middle2 : Fin 16) :
    (∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
        (T := sixVertexFourByFourTorus) ![
          sixVertexFourRowOfIndex middle0,
          sixVertexFourRowOfIndex opposite,
          sixVertexFourRowOfIndex middle2,
          sixVertexFourRowOfIndex seam] j) =
      sixVertexFourTwoStepWeight seam middle0 opposite *
        sixVertexFourTwoStepWeight opposite middle2 seam := by
  let indices : Fin 4 → Fin 16 := ![middle0, opposite, middle2, seam]
  let vertical : Fin 4 → SixVertexRow 4 := ![
    sixVertexFourRowOfIndex middle0,
    sixVertexFourRowOfIndex opposite,
    sixVertexFourRowOfIndex middle2,
    sixVertexFourRowOfIndex seam]
  let f : Fin 4 → Nat := fun j =>
    sixVertexHorizontalTransitionWitnessCountExecutable
      (T := sixVertexFourByFourTorus) vertical j
  let g : Fin 4 → Nat := fun j =>
    sixVertexFourHorizontalTransitionCount
      (indices (SixVertexArrows.cyclicPred
        sixVertexFourByFourTorus.height_pos j)) (indices j)
  change (∏ j, f j) = _
  calc
    _ = ∏ j, g j := by
      apply Fintype.prod_equiv (Equiv.refl (Fin 4))
      intro j
      fin_cases j <;>
        simp only [f, g, vertical, indices,
          sixVertexHorizontalTransitionWitnessCountExecutable,
          sixVertexFourByFourTorus, SixVertexArrows.cyclicPred] <;>
        apply sixVertexFourHorizontalTransitionCount_certificate
    _ = sixVertexFourHorizontalTransitionCount seam middle0 *
          sixVertexFourHorizontalTransitionCount middle0 opposite *
          sixVertexFourHorizontalTransitionCount opposite middle2 *
          sixVertexFourHorizontalTransitionCount middle2 seam :=
      sixVertexFourTableProduct_explicit middle0 opposite middle2 seam
    _ = _ := by
      unfold sixVertexFourTwoStepWeight
      ac_rfl

theorem sixVertexFourCycleRowGradeCount_eq_indices
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourCycleRowGradeCount sector totalC =
      sixVertexFourCycleIndexGradeCountExpanded sector totalC := by
  symm
  unfold sixVertexFourCycleIndexGradeCountExpanded
    sixVertexFourCycleRowGradeCount
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro seam
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro opposite
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro middle0
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro middle2
  simp only [sixVertexFourRowIndexEquiv_apply]
  apply if_congr Iff.rfl
  · apply if_congr
    · constructor
      · intro hgrade
        exact (sixVertexFourVerticalRowsTotalC_eq_twoStepGrades
          seam opposite middle0 middle2).trans hgrade
      · intro hgrade
        exact (sixVertexFourVerticalRowsTotalC_eq_twoStepGrades
          seam opposite middle0 middle2).symm.trans hgrade
    · exact (sixVertexFourWitnessProduct_eq_twoStepWeights
        seam opposite middle0 middle2).symm
    · rfl
  · rfl

theorem sixVertexFourGradeCountExecutable_eq_cycleIndicesExpanded
    (sector : Fin 5) (totalC : Nat) :
      sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourCycleIndexGradeCountExpanded sector totalC :=
  (sixVertexFourGradeCountExecutable_eq_cycleRows sector totalC).trans
    (sixVertexFourCycleRowGradeCount_eq_indices sector totalC)

theorem sixVertexFourCycleIndexGradeCountExpanded_eq_factored
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourCycleIndexGradeCountExpanded sector totalC =
      sixVertexFourCycleIndexGradeCount sector totalC := by
  unfold sixVertexFourCycleIndexGradeCountExpanded
    sixVertexFourCycleIndexGradeCount
  apply Finset.sum_congr rfl
  intro seam _
  unfold sixVertexFourCycleIndexSeamGradeCount
  by_cases hsector :
      sixVertexUpCount (sixVertexFourRowOfIndex seam) = sector.val
  · rw [if_pos hsector]
    apply Finset.sum_congr rfl
    intro opposite _
    unfold sixVertexFourCycleIndexPairGradeCount
    simp only [hsector, if_true]
  · rw [if_neg hsector]
    simp only [hsector, if_false, Finset.sum_const_zero]

theorem sixVertexFourGradeCountExecutable_eq_cycleIndices
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourCycleIndexGradeCount sector totalC :=
  (sixVertexFourGradeCountExecutable_eq_cycleIndicesExpanded
    sector totalC).trans
      (sixVertexFourCycleIndexGradeCountExpanded_eq_factored sector totalC)

theorem sixVertexRowDistance_le_width
    {N : Nat} (first second : SixVertexRow N) :
    sixVertexRowDistance first second ≤ N := by
  unfold sixVertexRowDistance
  calc
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := Fintype.card_fin N

theorem sixVertexFourTwoStepGrade_lt_nine
    (start middle finish : Fin 16) :
    sixVertexFourTwoStepGrade start middle finish < 9 := by
  unfold sixVertexFourTwoStepGrade
  have hfirst := sixVertexRowDistance_le_width
    (sixVertexFourRowOfIndex start) (sixVertexFourRowOfIndex middle)
  have hsecond := sixVertexRowDistance_le_width
    (sixVertexFourRowOfIndex middle) (sixVertexFourRowOfIndex finish)
  omega

theorem sixVertexFourTwoStepFactor_eq_countNat
    (start finish : Fin 16) (grade : Nat) :
    (∑ middle : Fin 16,
      if sixVertexFourTwoStepGrade start middle finish = grade then
        sixVertexFourTwoStepWeight start middle finish else 0) =
      sixVertexFourTwoStepCountNat start finish grade := by
  by_cases hgrade : grade < 9
  · rw [sixVertexFourTwoStepCountNat, dif_pos hgrade]
    rw [← sixVertexFourTwoStepCountTable_certificate]
    rfl
  · rw [sixVertexFourTwoStepCountNat, dif_neg hgrade]
    apply Finset.sum_eq_zero
    intro middle _
    rw [if_neg]
    intro heq
    have hlt := sixVertexFourTwoStepGrade_lt_nine start middle finish
    omega

set_option maxHeartbeats 5000000 in

theorem sixVertexFourTwoStepPairConvolution
    (seam opposite : Fin 16) (totalC : Nat) :
    (∑ middle0 : Fin 16, ∑ middle2 : Fin 16,
      if sixVertexFourTwoStepGrade seam middle0 opposite +
          sixVertexFourTwoStepGrade opposite middle2 seam = totalC then
        sixVertexFourTwoStepWeight seam middle0 opposite *
          sixVertexFourTwoStepWeight opposite middle2 seam
      else 0) =
      ∑ grade : Fin (totalC + 1),
        sixVertexFourTwoStepCountNat seam opposite grade.val *
          sixVertexFourTwoStepCountNat opposite seam
            (totalC - grade.val) := by
  calc
    _ = ∑ grade : Fin (totalC + 1),
          (∑ middle0 : Fin 16,
            if sixVertexFourTwoStepGrade seam middle0 opposite = grade.val
            then sixVertexFourTwoStepWeight seam middle0 opposite else 0) *
          (∑ middle2 : Fin 16,
            if sixVertexFourTwoStepGrade opposite middle2 seam =
                totalC - grade.val
            then sixVertexFourTwoStepWeight opposite middle2 seam else 0) :=
      fintypeWeightedGradeConvolution
        (fun middle0 : Fin 16 =>
          sixVertexFourTwoStepGrade seam middle0 opposite)
        (fun middle2 : Fin 16 =>
          sixVertexFourTwoStepGrade opposite middle2 seam)
        (fun middle0 : Fin 16 =>
          sixVertexFourTwoStepWeight seam middle0 opposite)
        (fun middle2 : Fin 16 =>
          sixVertexFourTwoStepWeight opposite middle2 seam)
        totalC
    _ = _ := by
      apply Finset.sum_congr rfl
      intro grade _
      rw [sixVertexFourTwoStepFactor_eq_countNat,
        sixVertexFourTwoStepFactor_eq_countNat]

set_option maxHeartbeats 5000000 in

theorem sixVertexFourCycleIndexGradeCount_eq_dynamic
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourCycleIndexGradeCount sector totalC =
      sixVertexFourDynamicGradeCount sector totalC := by
  unfold sixVertexFourCycleIndexGradeCount sixVertexFourDynamicGradeCount
  apply Finset.sum_congr rfl
  intro seam _
  unfold sixVertexFourCycleIndexSeamGradeCount
  unfold sixVertexFourDynamicSeamGradeCount
  apply if_congr Iff.rfl
  · apply Finset.sum_congr rfl
    intro opposite _
    unfold sixVertexFourCycleIndexPairGradeCount
    unfold sixVertexFourDynamicPairGradeCount
    exact sixVertexFourTwoStepPairConvolution seam opposite totalC
  · rfl

theorem sixVertexFourGradeCountExecutable_eq_dynamic
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourDynamicGradeCount sector totalC :=
  (sixVertexFourGradeCountExecutable_eq_cycleIndices sector totalC).trans
    (sixVertexFourCycleIndexGradeCount_eq_dynamic sector totalC)

end StatMech.FrontierD
