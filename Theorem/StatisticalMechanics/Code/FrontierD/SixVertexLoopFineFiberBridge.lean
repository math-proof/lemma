/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexConfigurationPairTotalC_eq_fineProfileGrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    {profile : SixVertexHorizontalBoundedFineRowProfile T}
    (pair : SixVertexConfigurationPairFineProfileFiber
      T left right profile) :
    sixVertexConfigurationPairTotalC pair.1 =
      (sixVertexHorizontalFineRowProfileGrade profile).1 := by
  have hgrade := sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade
    pair.1
  have hfine := sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade
    (pair.1.1.1.horizontal, pair.1.2.1.horizontal)
  rw [pair.2] at hfine
  exact congrArg Prod.fst (hgrade.trans hfine)


theorem card_sixVertexConfigurationPairFineProfileFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (profile : SixVertexHorizontalBoundedFineRowProfile T) :
    Fintype.card
        (SixVertexConfigurationPairFineProfileFiber T left right profile) =
      sixVertexHorizontalFineRowProfileSectorPairSum
        T left right profile := by
  rw [Fintype.card_congr
    (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions
      T left right profile)]
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_prod,
    card_sixVertexHorizontalSectorCompletion_eq_chooseCount]
  unfold sixVertexHorizontalFineRowProfileSectorPairSum
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun horizontal :
      SixVertexHorizontalField T × SixVertexHorizontalField T =>
        sixVertexHorizontalPairBoundedFineRowProfile horizontal = profile)
    (by simp)
    (fun horizontal =>
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2)]
  rw [Finset.sum_filter]


end
end StatMech.FrontierD
