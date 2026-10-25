/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairProfileMultiplicity_swapLayers
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexSwapHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberSwapLayersEquiv T grade profile).symm


theorem sixVertexHorizontalChooseSum_reflectFirst
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T left) horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount
            T right horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectFirstHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectFirst]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectFirstHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectFirst]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T left)
        (sixVertexReflectHorizontalField horizontal.1.1) *
      sixVertexHorizontalSectorCompletionChooseCount
        T right horizontal.1.2
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalComplementSector_involutive]


theorem sixVertexHorizontalChooseSum_reflectSecond
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount
          T right horizontal.1.2) =
      ∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
        sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
          sixVertexHorizontalSectorCompletionChooseCount T
            (sixVertexHorizontalComplementSector T right)
            horizontal.1.2 := by
  let reflect :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} ≃
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} :=
    { toFun := fun horizontal =>
        ⟨sixVertexReflectSecondHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectSecond]
          exact horizontal.2⟩
      invFun := fun horizontal =>
        ⟨sixVertexReflectSecondHorizontalLayer horizontal.1, by
          rw [sixVertexHorizontalPairBigrade_reflectSecond]
          exact horizontal.2⟩
      left_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1
      right_inv := fun horizontal => by
        apply Subtype.ext
        exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1 }
  apply Fintype.sum_equiv reflect
  intro horizontal
  change _ =
    sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
      sixVertexHorizontalSectorCompletionChooseCount T
        (sixVertexHorizontalComplementSector T right)
        (sixVertexReflectHorizontalField horizontal.1.2)
  rw [sixVertexHorizontalSectorCompletionChooseCount_reflect,
    sixVertexHorizontalComplementSector_involutive]


theorem horizontalChooseBigradeFibers_iff_diagonal_of_complement
    (T : EvenTorus)
    (lower upper middle : Fin (T.width + 1))
    (hcomplement : sixVertexHorizontalComplementSector T lower = upper) :
    SixVertexHorizontalChooseBigradeFiberDominates
        T lower upper middle middle ↔
      forall grade,
        (∑ horizontal :
            {horizontal : SixVertexHorizontalField T ×
                SixVertexHorizontalField T //
              sixVertexHorizontalPairBigrade horizontal = grade},
          sixVertexHorizontalSectorCompletionChooseCount
              T upper horizontal.1.1 *
            sixVertexHorizontalSectorCompletionChooseCount
              T upper horizontal.1.2) <=
          ∑ horizontal :
            {horizontal : SixVertexHorizontalField T ×
                SixVertexHorizontalField T //
              sixVertexHorizontalPairBigrade horizontal = grade},
            sixVertexHorizontalSectorCompletionChooseCount
                T middle horizontal.1.1 *
              sixVertexHorizontalSectorCompletionChooseCount
                T middle horizontal.1.2 := by
  unfold SixVertexHorizontalChooseBigradeFiberDominates
  constructor
  · intro hdom grade
    have hreflect :=
      sixVertexHorizontalChooseSum_reflectFirst T lower upper grade
    rw [hcomplement] at hreflect
    rw [← hreflect]
    exact hdom grade
  · intro hdom grade
    have hreflect :=
      sixVertexHorizontalChooseSum_reflectFirst T lower upper grade
    rw [hcomplement] at hreflect
    rw [hreflect]
    exact hdom grade

end
end StatMech.FrontierD
