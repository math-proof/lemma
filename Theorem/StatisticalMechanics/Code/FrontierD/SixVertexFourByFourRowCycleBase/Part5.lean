/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowCycleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowCycleBase.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFourByFourVertical_last
    (row0 row1 row2 row3 : SixVertexRow 4) :
    (![
      row0, row1, row2, row3] : Fin 4 → SixVertexRow 4)
        (svFinLast sixVertexFourByFourTorus.height_pos) = row3 := by
  rfl

theorem sixVertexFourByFourWitnessProduct_certificate
    (index0 index1 index2 index3 : Fin 16) :
    let vertical : Fin 4 → SixVertexRow 4 := ![
      sixVertexFourRowOfIndex index0,
      sixVertexFourRowOfIndex index1,
      sixVertexFourRowOfIndex index2,
      sixVertexFourRowOfIndex index3]
    (∏ j, sixVertexHorizontalTransitionWitnessCountExecutable
        (T := sixVertexFourByFourTorus) vertical j) =
      ∏ j, sixVertexFourHorizontalTransitionCount
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16)
          (SixVertexArrows.cyclicPred
            sixVertexFourByFourTorus.height_pos j))
        ((![index0, index1, index2, index3] : Fin 4 → Fin 16) j) := by
  dsimp only
  apply Finset.prod_congr rfl
  intro j _
  fin_cases j <;>
    simp only [sixVertexHorizontalTransitionWitnessCountExecutable,
      sixVertexFourByFourTorus, SixVertexArrows.cyclicPred,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;>
    apply sixVertexFourHorizontalTransitionCount_certificate

theorem sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached
    (sector : Fin 5) (totalC : Nat) :
    sixVertexFourByFourRowCycleGradeCountExecutable sector totalC =
      sixVertexFourByFourCachedGradeCount sector totalC := by
  symm
  unfold sixVertexFourByFourCachedGradeCount
    sixVertexFourByFourRowCycleGradeCountExecutable
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index0
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index1
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index2
  apply Fintype.sum_equiv sixVertexFourRowIndexEquiv
  intro index3
  simp only [sixVertexFourRowIndexEquiv_apply]
  simp only [sixVertexFourByFourVertical_last]
  apply if_congr Iff.rfl
  · apply if_congr Iff.rfl
    · exact (sixVertexFourByFourWitnessProduct_certificate
        index0 index1 index2 index3).symm
    · rfl
  · rfl

theorem sixVertexFourByFourGradeCountExecutable_eq_cached
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourCachedGradeCount sector totalC :=
  (sixVertexFourByFourGradeCountExecutable_eq_rows sector totalC).trans
    (sixVertexFourByFourRowCycleGradeCountExecutable_eq_cached sector totalC)

theorem sixVertexHorizontalTransitionWitnessCountExecutable_eq_card
    {T : EvenTorus} (vertical : Fin T.height → SixVertexRow T.width)
    (j : Fin T.height) :
    sixVertexHorizontalTransitionWitnessCountExecutable vertical j =
      Nat.card (SixVertexHorizontalTransitionWitness vertical j) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem sixVertexMarkedSectorRowCycleGradeCountExecutable_eq
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCountExecutable T sector totalC =
      sixVertexMarkedSectorRowCycleGradeCount T sector totalC := by
  let p : (Fin T.height → SixVertexRow T.width) → Prop := fun vertical =>
    sixVertexUpCount (vertical (svFinLast T.height_pos)) = sector.val
  let f : (Fin T.height → SixVertexRow T.width) → Nat := fun vertical =>
    if sixVertexVerticalRowsTotalC vertical = totalC then
      ∏ j, sixVertexHorizontalTransitionWitnessCountExecutable vertical j
    else 0
  unfold sixVertexMarkedSectorRowCycleGradeCountExecutable
    sixVertexMarkedSectorRowCycleGradeCount
  simp only [← Nat.card_eq_fintype_card]
  change
    (∑ vertical : Fin T.height → SixVertexRow T.width,
      if p vertical then f vertical else 0) =
        ∑ vertical : Subtype p,
          if sixVertexVerticalRowsTotalC vertical.1 = totalC then
            ∏ j, Nat.card
              (SixVertexHorizontalTransitionWitness vertical.1 j)
          else 0
  calc
    _ = Finset.sum
        ((Finset.univ : Finset (Fin T.height → SixVertexRow T.width)).filter p)
        f := (Finset.sum_filter p f).symm
    _ = ∑ vertical : Subtype p, f vertical.1 :=
      Finset.sum_subtype
        ((Finset.univ : Finset (Fin T.height → SixVertexRow T.width)).filter p)
        (by intro vertical; simp [p]) f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro vertical _
      by_cases hgrade : sixVertexVerticalRowsTotalC vertical.1 = totalC
      · simp only [f, hgrade, if_true]
        apply Finset.prod_congr rfl
        intro j _
        exact sixVertexHorizontalTransitionWitnessCountExecutable_eq_card
          vertical.1 j
      · simp only [f, hgrade, if_false]

end
end StatMech.FrontierD
