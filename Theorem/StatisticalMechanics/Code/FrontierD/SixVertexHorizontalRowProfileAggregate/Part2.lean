/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem rowProfileResidualCapacity_iff_signedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)) :
    SixVertexHorizontalRowProfileResidualCapacity T
        sourceLeft sourceRight targetLeft targetRight <->
      SixVertexHorizontalRowProfileAggregateSignedNonnegative T
        sourceLeft sourceRight targetLeft targetRight := by
  unfold SixVertexHorizontalRowProfileResidualCapacity
    SixVertexHorizontalRowProfileAggregateSignedNonnegative
  constructor <;> intro h grade rowProfile
  · have hcard := h grade rowProfile
    rw [card_sixVertexHorizontalActualDeficitRowProfileFiber,
      card_sixVertexHorizontalActualSurplusRowProfileFiber] at hcard
    have hsplit :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) -
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      unfold sixVertexHorizontalProfileSignedKernel
        sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      exact (Int.toNat_sub_toNat_neg _).symm
    rw [hsplit]
    have hcard' :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) <=
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      exact_mod_cast hcard
    omega
  · rw [card_sixVertexHorizontalActualDeficitRowProfileFiber,
      card_sixVertexHorizontalActualSurplusRowProfileFiber]
    have hsigned := h grade rowProfile
    have hsplit :
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          sixVertexHorizontalProfileSignedKernel
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
        (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileSurplus
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) -
        ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
          T grade rowProfile,
          (sixVertexHorizontalProfileDeficit
            sourceLeft sourceRight targetLeft targetRight
            (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      unfold sixVertexHorizontalProfileSignedKernel
        sixVertexHorizontalProfileSurplus
        sixVertexHorizontalProfileDeficit
      exact (Int.toNat_sub_toNat_neg _).symm
    rw [hsplit] at hsigned
    have hcard :
      (∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile,
        (sixVertexHorizontalProfileDeficit
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int)) <=
      ∑ horizontal : SixVertexHorizontalPairRowBigradeFiber
        T grade rowProfile,
        (sixVertexHorizontalProfileSurplus
          sourceLeft sourceRight targetLeft targetRight
          (sixVertexHorizontalPairCompletionProfile T horizontal.1) : Int) := by
      omega
    exact_mod_cast hcard


theorem configurationBigradeFibers_of_rowProfileSignedNonnegative
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexConfigurationPairBigradeFiberDominates T
      sourceLeft sourceRight targetLeft targetRight := by
  apply configurationBigradeFibers_of_rowProfileResidualCapacity T
  exact (rowProfileResidualCapacity_iff_signedNonnegative T
    sourceLeft sourceRight targetLeft targetRight).mpr hsigned


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hsigned : SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    T middle hmiddle_pos hmiddle_lt
      (configurationBigradeFibers_of_rowProfileSignedNonnegative T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hsigned)

end
end StatMech.FrontierD
