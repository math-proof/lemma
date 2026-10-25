/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    {T : EvenTorus}
    {first second : SixVertexHorizontalField T ×
      SixVertexHorizontalField T}
    (h : sixVertexHorizontalPairFineRowProfile first =
      sixVertexHorizontalPairFineRowProfile second) :
    sixVertexHorizontalPairBoundedFineRowProfile first =
      sixVertexHorizontalPairBoundedFineRowProfile second := by
  funext j
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst (congrFun h j)
  · exact congrArg Prod.snd (congrFun h j)

theorem sum_sixVertexHorizontalRowNontransitionCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalRowNontransitionCount horizontal j) =
      sixVertexHorizontalNontransitionCount horizontal := by
  unfold sixVertexHorizontalRowNontransitionCount
    sixVertexHorizontalNontransitionCount
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_sixVertexHorizontalPairRowNontransitionProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalPairRowNontransitionProfile horizontal j) =
      sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 := by
  unfold sixVertexHorizontalPairRowNontransitionProfile
  rw [Finset.sum_add_distrib,
    sum_sixVertexHorizontalRowNontransitionCount,
    sum_sixVertexHorizontalRowNontransitionCount]

theorem sixVertexHorizontalRowNontransitionCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowNontransitionCount
        (sixVertexReflectHorizontalField horizontal) j =
      sixVertexHorizontalRowNontransitionCount horizontal j := by
  let xEquiv : Fin T.width ≃ Fin T.width :=
    (sixVertexCyclicNegEquiv T.width_pos).trans
      (svFinitePeriodicSuccEquiv T.width_pos)
  unfold sixVertexHorizontalRowNontransitionCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal)
            (SixVertexArrows.cyclicPred T.width_pos i, j) =
          sixVertexHorizontalGaugeBit
            (sixVertexReflectHorizontalField horizontal) (i, j)
      then 1 else 0) =
        ∑ i : Fin T.width,
          if sixVertexHorizontalGaugeBit horizontal
                (SixVertexArrows.cyclicPred T.width_pos (xEquiv i), j) =
              sixVertexHorizontalGaugeBit horizontal (xEquiv i, j)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sixVertexHorizontalGaugeBit_reflect,
        sixVertexHorizontalGaugeBit_reflect]
      have hnegPred := sixVertexCyclicNeg_cyclicPred T.width_pos i
      have hpredSucc := svCyclicPred_finitePeriodicSucc
        T.width_pos (sixVertexCyclicNeg T.width_pos i)
      change (if sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos
              (SixVertexArrows.cyclicPred T.width_pos i), j) =
          sixVertexHorizontalGaugeBit horizontal
            (sixVertexCyclicNeg T.width_pos i, j)
        then 1 else 0) = _
      rw [hnegPred]
      have hxi : xEquiv i = finitePeriodicSucc T.width_pos
          (sixVertexCyclicNeg T.width_pos i) := by rfl
      rw [hxi, hpredSucc]
      simp only [eq_comm]
    _ = _ := by
      exact xEquiv.sum_comp fun i =>
        if sixVertexHorizontalGaugeBit horizontal
              (SixVertexArrows.cyclicPred T.width_pos i, j) =
            sixVertexHorizontalGaugeBit horizontal (i, j)
        then 1 else 0

theorem sixVertexHorizontalPairRowNontransitionProfile_eq_sum
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) (j : Fin T.height) :
    sixVertexHorizontalPairRowNontransitionProfile horizontal j =
      ∑ i : Fin T.width,
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j) := by
  unfold sixVertexHorizontalPairRowNontransitionProfile
    sixVertexHorizontalRowNontransitionCount
    sixVertexHorizontalPairBondAgreementCount boolPairAgreementCount
  rw [Finset.sum_add_distrib]

theorem sixVertexSwitchHorizontalPair_rowNontransitionProfile
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) (j : Fin T.height) :
    sixVertexHorizontalPairRowNontransitionProfile
        (sixVertexSwitchHorizontalPair mask horizontal) j =
      ∑ i : Fin T.width,
        if mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i
        then sixVertexHorizontalPairBondAgreementCount horizontal (i, j)
        else sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j) := by
  rw [sixVertexHorizontalPairRowNontransitionProfile_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact sixVertexSwitchHorizontalPair_bondAgreement mask horizontal (i, j)


end
end StatMech.FrontierD
