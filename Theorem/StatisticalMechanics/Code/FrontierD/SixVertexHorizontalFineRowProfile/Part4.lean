/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem rowProfileSignedNonnegative_of_fineRowProfile
    (T : EvenTorus)
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight) :
    SixVertexHorizontalRowProfileAggregateSignedNonnegative T
      sourceLeft sourceRight targetLeft targetRight := by
  intro grade rowProfile
  let signature := fun horizontal :
      SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
    sixVertexHorizontalPairBoundedFineRowProfile horizontal.1
  let kernel := fun horizontal :
      SixVertexHorizontalPairRowBigradeFiber T grade rowProfile =>
    sixVertexHorizontalProfileSignedKernel
      sourceLeft sourceRight targetLeft targetRight
      (sixVertexHorizontalPairCompletionProfile T horizontal.1)
  rw [← Finset.sum_fiberwise
    (Finset.univ : Finset
      (SixVertexHorizontalPairRowBigradeFiber T grade rowProfile))
    signature kernel]
  apply Finset.sum_nonneg
  intro fineProfile hfineProfile
  simpa [signature, kernel] using hfine grade rowProfile fineProfile


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_rowProfileSigned
    T middle hmiddle_pos hmiddle_lt
      (rowProfileSignedNonnegative_of_fineRowProfile T
        ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
        middle middle hfine)

end
end StatMech.FrontierD
