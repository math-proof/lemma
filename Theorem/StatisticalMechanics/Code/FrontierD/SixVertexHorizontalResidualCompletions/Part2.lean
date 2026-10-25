/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalActualDeficitConfigurationPair_injective
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexHorizontalActualDeficitConfigurationPair :
        SixVertexHorizontalActualDeficitTokens T grade
            sourceLeft sourceRight targetLeft targetRight ->
          {pair : SixVertexMarkedSectorConfiguration T sourceLeft ×
              SixVertexMarkedSectorConfiguration T sourceRight //
            sixVertexConfigurationPairBigrade pair = grade}) := by
  rintro ⟨firstProfile, ⟨firstFiber, firstIndex⟩⟩
    ⟨secondProfile, ⟨secondFiber, secondIndex⟩⟩ heq
  let first : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨firstProfile, firstFiber, firstIndex⟩
  let second : SixVertexHorizontalActualDeficitTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨secondProfile, secondFiber, secondIndex⟩
  change sixVertexHorizontalActualDeficitConfigurationPair first =
    sixVertexHorizontalActualDeficitConfigurationPair second at heq
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T sourceLeft sourceRight grade
  have hcoordinates := congrArg coordinateEquiv heq
  simp only [coordinateEquiv,
    sixVertexHorizontalActualDeficitConfigurationPair,
    Equiv.apply_symm_apply] at hcoordinates
  have hhorizontal : first.2.1.1 = second.2.1.1 :=
    congrArg Sigma.fst hcoordinates
  have hhorizontalValue : first.2.1.1.1 = second.2.1.1.1 :=
    congrArg Subtype.val hhorizontal
  have hprofile : firstProfile = secondProfile :=
    firstFiber.2.symm.trans ((congrArg
      (sixVertexHorizontalPairCompletionProfile T) hhorizontalValue).trans
        secondFiber.2)
  cases hprofile
  refine Sigma.ext rfl (heq_of_eq ?_)
  have hfiber : firstFiber = secondFiber := by
    apply Subtype.ext
    exact hhorizontal
  apply Prod.ext
  · exact hfiber
  · subst hfiber
    have hcompletion := eq_of_heq (Sigma.ext_iff.mp hcoordinates).2
    apply (sixVertexHorizontalDeficitCompletionEmbedding sourceLeft
      sourceRight targetLeft targetRight firstProfile firstFiber).injective
    simpa only [first, second,
      sixVertexHorizontalActualDeficitCompletionPair] using hcompletion


theorem sixVertexHorizontalActualSurplusConfigurationPair_injective
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
    Function.Injective
      (sixVertexHorizontalActualSurplusConfigurationPair :
        SixVertexHorizontalActualSurplusTokens T grade
            sourceLeft sourceRight targetLeft targetRight ->
          {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
              SixVertexMarkedSectorConfiguration T targetRight //
            sixVertexConfigurationPairBigrade pair = grade}) := by
  rintro ⟨firstProfile, ⟨firstFiber, firstIndex⟩⟩
    ⟨secondProfile, ⟨secondFiber, secondIndex⟩⟩ heq
  let first : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨firstProfile, firstFiber, firstIndex⟩
  let second : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨secondProfile, secondFiber, secondIndex⟩
  change sixVertexHorizontalActualSurplusConfigurationPair first =
    sixVertexHorizontalActualSurplusConfigurationPair second at heq
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T targetLeft targetRight grade
  have hcoordinates := congrArg coordinateEquiv heq
  simp only [coordinateEquiv,
    sixVertexHorizontalActualSurplusConfigurationPair,
    Equiv.apply_symm_apply] at hcoordinates
  have hhorizontal : first.2.1.1 = second.2.1.1 :=
    congrArg Sigma.fst hcoordinates
  have hhorizontalValue : first.2.1.1.1 = second.2.1.1.1 :=
    congrArg Subtype.val hhorizontal
  have hprofile : firstProfile = secondProfile :=
    firstFiber.2.symm.trans ((congrArg
      (sixVertexHorizontalPairCompletionProfile T) hhorizontalValue).trans
        secondFiber.2)
  cases hprofile
  refine Sigma.ext rfl (heq_of_eq ?_)
  have hfiber : firstFiber = secondFiber := by
    apply Subtype.ext
    exact hhorizontal
  apply Prod.ext
  · exact hfiber
  · subst hfiber
    have hcompletion := eq_of_heq (Sigma.ext_iff.mp hcoordinates).2
    apply (sixVertexHorizontalSurplusCompletionEmbedding sourceLeft
      sourceRight targetLeft targetRight firstProfile firstFiber).injective
    simpa only [first, second,
      sixVertexHorizontalActualSurplusCompletionPair] using hcompletion


theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight
      (sixVertexHorizontalPairCompletionProfile T
        ((sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
          T targetLeft targetRight grade) configuration).1.1) = 0) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  let coordinateEquiv :=
    sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions
      T targetLeft targetRight grade
  let coordinates := coordinateEquiv configuration
  let horizontal := coordinates.1
  let completions := coordinates.2
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1.1) :=
    Subtype.fintype _
  letI : Fintype (SixVertexVerticalCompletion T horizontal.1.2) :=
    Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetLeft horizontal.1.1) := Subtype.fintype _
  letI : Fintype (SixVertexHorizontalSectorCompletion
      T targetRight horizontal.1.2) := Subtype.fintype _
  let profile := sixVertexHorizontalPairCompletionProfile T horizontal.1
  let fiber : SixVertexHorizontalPairProfileFiber T grade profile :=
    ⟨horizontal, rfl⟩
  let completionEquiv := Fintype.equivFin
    (SixVertexHorizontalPairSectorCompletions
      T targetLeft targetRight horizontal.1)
  have hsurplus :
      sixVertexHorizontalProfileSurplus sourceLeft sourceRight
          targetLeft targetRight profile =
        Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal.1) := by
    rw [sixVertexHorizontalProfileSurplus_eq_sub, hzero]
    simp only [Nat.sub_zero]
    calc
      sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile =
          sixVertexHorizontalSectorCompletionChooseCount
              T targetLeft horizontal.1.1 *
            sixVertexHorizontalSectorCompletionChooseCount
              T targetRight horizontal.1.2 := by
        exact (sixVertexHorizontalPairChooseWeight_eq_profile
          T targetLeft targetRight horizontal.1).symm
      _ = Fintype.card (SixVertexHorizontalPairSectorCompletions
          T targetLeft targetRight horizontal.1) := by
        rw [Fintype.card_prod]
        exact congrArg₂ (fun a b : Nat => a * b)
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetLeft horizontal.1.1).symm
          (card_sixVertexHorizontalSectorCompletion_eq_chooseCount
            T targetRight horizontal.1.2).symm
  let index : Fin (sixVertexHorizontalProfileSurplus sourceLeft sourceRight
      targetLeft targetRight profile) :=
    ⟨(completionEquiv completions).val, by
      rw [hsurplus]
      exact (completionEquiv completions).isLt⟩
  let token : SixVertexHorizontalActualSurplusTokens T grade
      sourceLeft sourceRight targetLeft targetRight :=
    ⟨profile, fiber, index⟩
  refine ⟨token, ?_⟩
  apply coordinateEquiv.injective
  change Sigma.mk horizontal
      (sixVertexHorizontalActualSurplusCompletionPair token) = coordinates
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change (sixVertexHorizontalSurplusCompletionEmbedding sourceLeft sourceRight
      targetLeft targetRight profile fiber) index = completions
    change completionEquiv.symm ⟨index.val, _⟩ = completions
    apply completionEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl


theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hzero : sixVertexHorizontalPairProfileChooseWeight
      sourceLeft sourceRight
      (sixVertexHorizontalPairCompletionProfile T
        (configuration.1.1.1.horizontal,
          configuration.1.2.1.horizontal)) = 0) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero
  exact hzero


theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_left_isEmpty
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T sourceLeft
      configuration.1.1.1.horizontal)) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    sourceLeft sourceRight
      (configuration.1.1.1.horizontal, configuration.1.2.1.horizontal) hleft


theorem
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_right_isEmpty
    {T : EvenTorus} {grade : Nat × Nat}
    {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
    (configuration :
      {pair : SixVertexMarkedSectorConfiguration T targetLeft ×
          SixVertexMarkedSectorConfiguration T targetRight //
        sixVertexConfigurationPairBigrade pair = grade})
    (hright : IsEmpty (SixVertexHorizontalSectorCompletion T sourceRight
      configuration.1.2.1.horizontal)) :
    ∃ token : SixVertexHorizontalActualSurplusTokens T grade
        sourceLeft sourceRight targetLeft targetRight,
      sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
  apply
    sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero
  exact sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
    sourceLeft sourceRight
      (configuration.1.1.1.horizontal, configuration.1.2.1.horizontal) hright

end
end StatMech.FrontierD
