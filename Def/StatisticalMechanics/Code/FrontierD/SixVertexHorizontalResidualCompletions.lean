/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexHorizontalDeficitCompletionEmbedding
    {T : EvenTorus} {grade : Nat × Nat}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T)
    (fiber : SixVertexHorizontalPairProfileFiber T grade profile) :
    Fin (sixVertexHorizontalProfileDeficit sourceLeft sourceRight
      targetLeft targetRight profile) ↪
      SixVertexHorizontalPairSectorCompletions T sourceLeft sourceRight
        fiber.1.1 := by
  let horizontal := fiber.1.1
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T sourceLeft horizontal.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T sourceRight horizontal.2) := Subtype.fintype _
  have hprofile :
      sixVertexHorizontalPairCompletionProfile T horizontal = profile :=
    fiber.2
  have hindex (index : Fin (sixVertexHorizontalProfileDeficit
      sourceLeft sourceRight targetLeft targetRight profile)) : index.val <
      Fintype.card (SixVertexHorizontalPairSectorCompletions
        T sourceLeft sourceRight horizontal) := by
    calc
      index.val < sixVertexHorizontalProfileDeficit sourceLeft sourceRight
          targetLeft targetRight profile := index.isLt
      _ <= sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile := by
        rw [sixVertexHorizontalProfileDeficit_eq_sub]
        exact Nat.sub_le _ _
      _ = sixVertexHorizontalSectorCompletionChooseCount
            T sourceLeft horizontal.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T sourceRight horizontal.2 := by
        rw [sixVertexHorizontalPairChooseWeight_eq_profile, hprofile]
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T sourceLeft sourceRight horizontal) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T sourceLeft horizontal.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T sourceRight horizontal.2).symm
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T sourceLeft sourceRight horizontal)
  refine
    { toFun := fun index => completionEquiv.symm ⟨index.val, hindex index⟩
      inj' := ?_ }
  intro first second heq
  apply Fin.ext
  have hindexEq := congrArg completionEquiv heq
  simpa only [Equiv.apply_symm_apply] using congrArg Fin.val hindexEq


noncomputable def sixVertexHorizontalSurplusCompletionEmbedding
    {T : EvenTorus} {grade : Nat × Nat}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T)
    (fiber : SixVertexHorizontalPairProfileFiber T grade profile) :
    Fin (sixVertexHorizontalProfileSurplus sourceLeft sourceRight
      targetLeft targetRight profile) ↪
      SixVertexHorizontalPairSectorCompletions T targetLeft targetRight
        fiber.1.1 := by
  let horizontal := fiber.1.1
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetLeft horizontal.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetRight horizontal.2) := Subtype.fintype _
  have hprofile :
      sixVertexHorizontalPairCompletionProfile T horizontal = profile :=
    fiber.2
  have hindex (index : Fin (sixVertexHorizontalProfileSurplus
      sourceLeft sourceRight targetLeft targetRight profile)) : index.val <
      Fintype.card (SixVertexHorizontalPairSectorCompletions
        T targetLeft targetRight horizontal) := by
    calc
      index.val < sixVertexHorizontalProfileSurplus sourceLeft sourceRight
          targetLeft targetRight profile := index.isLt
      _ <= sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile := by
        rw [sixVertexHorizontalProfileSurplus_eq_sub]
        exact Nat.sub_le _ _
      _ = sixVertexHorizontalSectorCompletionChooseCount
            T targetLeft horizontal.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T targetRight horizontal.2 := by
        rw [sixVertexHorizontalPairChooseWeight_eq_profile, hprofile]
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetLeft horizontal.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetRight horizontal.2).symm
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T targetLeft targetRight horizontal)
  refine
    { toFun := fun index => completionEquiv.symm ⟨index.val, hindex index⟩
      inj' := ?_ }
  intro first second heq
  apply Fin.ext
  have hindexEq := congrArg completionEquiv heq
  simpa only [Equiv.apply_symm_apply] using congrArg Fin.val hindexEq

noncomputable def sixVertexHorizontalActualDeficitCompletionPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalPairSectorCompletions T sourceLeft sourceRight
      (sixVertexHorizontalActualDeficitPair token) :=
  sixVertexHorizontalDeficitCompletionEmbedding sourceLeft sourceRight
    targetLeft targetRight token.1 token.2.1 token.2.2

noncomputable def sixVertexHorizontalActualSurplusCompletionPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalPairSectorCompletions T targetLeft targetRight
      (sixVertexHorizontalActualSurplusPair token) :=
  sixVertexHorizontalSurplusCompletionEmbedding sourceLeft sourceRight
    targetLeft targetRight token.1 token.2.1 token.2.2

noncomputable def sixVertexHorizontalActualDeficitConfigurationPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
        SixVertexMarkedSectorConfiguration T sourceRight //
      sixVertexConfigurationPairBigrade pair = grade} :=
  (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    T sourceLeft sourceRight grade).symm
      ⟨token.2.1.1,
        sixVertexHorizontalActualDeficitCompletionPair token⟩

noncomputable def sixVertexHorizontalActualSurplusConfigurationPair
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight) :
    {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
        SixVertexMarkedSectorConfiguration T targetRight //
      sixVertexConfigurationPairBigrade pair = grade} :=
  (sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
    T targetLeft targetRight grade).symm
      ⟨token.2.1.1,
        sixVertexHorizontalActualSurplusCompletionPair token⟩


end
end StatMech.FrontierD
