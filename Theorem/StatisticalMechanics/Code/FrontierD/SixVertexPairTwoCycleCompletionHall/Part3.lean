/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleHall.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3


namespace StatMech.FrontierD

noncomputable section

theorem horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hunion : SixVertexHorizontalFineProfileCompletionUnionMatching
      T lower middle upper) :
    SixVertexHorizontalFineProfileCompletionTwoCycleMatching
      T lower middle upper := by
  intro profile
  obtain ⟨matching, hinjective, hpreserves⟩ := hunion profile
  exact ⟨matching, hinjective,
    fun source => (hpreserves source).twoCycle⟩


theorem horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) :
    SixVertexHorizontalFineProfileCompletionTwoCycleMatching
        T lower middle upper <->
      SixVertexConfigurationPairTwoCycleFineProfileFiberHall
        T lower middle upper := by
  rw [configurationPairTwoCycleFineProfileFiberHall_iff]
  constructor
  · intro hcompletion profile
    obtain ⟨matching, hinjective, hrelated⟩ := hcompletion profile
    let sourceEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T lower upper profile
    let targetEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T middle middle profile
    let fiberMatching := fun source =>
      targetEquiv.symm (matching (sourceEquiv source))
    refine ⟨fiberMatching, ?_, ?_⟩
    · intro source₁ source₂ heq
      apply sourceEquiv.injective
      apply hinjective
      apply targetEquiv.symm.injective
      exact heq
    · intro source
      exact (fineProfileCompletionPairTwoCycleRelated_equiv_iff
        source (fiberMatching source)).mp (by
          change SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated
            (sourceEquiv source) (matching (sourceEquiv source))
          exact hrelated (sourceEquiv source))
  · intro hFiber profile
    obtain ⟨matching, hinjective, hrelated⟩ := hFiber profile
    let sourceEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T lower upper profile
    let targetEquiv :=
      sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
        T middle middle profile
    let completionMatching := fun source =>
      targetEquiv (matching (sourceEquiv.symm source))
    refine ⟨completionMatching, ?_, ?_⟩
    · intro source₁ source₂ heq
      apply sourceEquiv.symm.injective
      apply hinjective
      apply targetEquiv.injective
      exact heq
    · intro source
      exact (fineProfileCompletionPairTwoCycleRelated_equiv_iff
        (sourceEquiv.symm source)
        (matching (sourceEquiv.symm source))).mpr
          (hrelated (sourceEquiv.symm source))


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalFineProfileCompletionTwoCycleMatching T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
    T middle hmiddle_pos hmiddle_lt
  apply configurationPairTwoCycleFineHall_of_profileFiberHall
  exact (horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall
    T ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩).mp hmatching


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_unionMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalFineProfileCompletionUnionMatching T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching
    T middle hmiddle_pos hmiddle_lt
      (horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching
        hmatching)

end
end StatMech.FrontierD
