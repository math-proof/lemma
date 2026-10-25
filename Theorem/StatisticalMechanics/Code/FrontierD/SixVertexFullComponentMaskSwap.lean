/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexFullDisagreementMask.local_eq_disagreement
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex)
    (hactive : exists d,
      sixVertexTorusLocalSwitchMask mask v d = true) :
    forall r, sixVertexTorusLocalSwitchMask mask v r =
      decide (sixVertexLocalIncomingPattern omega v r ≠
        sixVertexLocalIncomingPattern eta v r) := by
  obtain ⟨d, hd⟩ := hactive
  intro r
  by_cases hr : sixVertexLocalIncomingPattern omega v r ≠
      sixVertexLocalIncomingPattern eta v r
  · rw [hmask.2 v d r hd hr]
    simp [hr]
  · have hfalse : sixVertexTorusLocalSwitchMask mask v r = false := by
      cases hm : sixVertexTorusLocalSwitchMask mask v r
      · rfl
      · exact False.elim (hr (hmask.1 v r hm))
    rw [hfalse]
    simp [hr]

theorem SixVertexFullDisagreementMask.local_eq_or_swap
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex) :
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
        (sixVertexLocalIncomingPattern omega v,
          sixVertexLocalIncomingPattern eta v) \/
    (sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchFirst mask omega eta) v,
      sixVertexLocalIncomingPattern
        (sixVertexTorusSwitchSecond mask omega eta) v) =
        (sixVertexLocalIncomingPattern eta v,
          sixVertexLocalIncomingPattern omega v) := by
  rw [sixVertexTorusLocalIncomingPattern_pairSwitch]
  by_cases hactive : exists d,
      sixVertexTorusLocalSwitchMask mask v d = true
  · right
    exact sixVertexLocalSwapMask_eq_pair_of_disagreementMask _ _ _
      (hmask.local_eq_disagreement v hactive)
  · left
    have hzero : sixVertexTorusLocalSwitchMask mask v = fun _ => false := by
      funext d
      cases hm : sixVertexTorusLocalSwitchMask mask v d
      · rfl
      · exact False.elim (hactive ⟨d, hm⟩)
    simp [sixVertexLocalSwapMask, hzero]

theorem SixVertexFullDisagreementMask.localCTypeCount
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask)
    (v : T.Vertex) :
    sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v)
        (sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v) =
      sixVertexLocalCTypeCount
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) := by
  rcases hmask.local_eq_or_swap v with hsame | hswap
  · rw [show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v =
        sixVertexLocalIncomingPattern omega v by
          exact congrArg Prod.fst hsame,
      show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v =
        sixVertexLocalIncomingPattern eta v by
          exact congrArg Prod.snd hsame]
  · rw [show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchFirst mask omega eta) v =
        sixVertexLocalIncomingPattern eta v by
          exact congrArg Prod.fst hswap,
      show sixVertexLocalIncomingPattern
          (sixVertexTorusSwitchSecond mask omega eta) v =
        sixVertexLocalIncomingPattern omega v by
          exact congrArg Prod.snd hswap]
    simp only [sixVertexLocalCTypeCount, add_comm]

theorem SixVertexFullDisagreementMask.boundedFineRowProfile
    {T : EvenTorus} {omega eta mask : SixVertexArrows T}
    (hmask : SixVertexFullDisagreementMask omega eta mask) :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        (omega.horizontal, eta.horizontal) := by
  apply sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
  funext j
  apply Prod.ext
  · change sixVertexHorizontalPairRowNontransitionProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) j =
      sixVertexHorizontalPairRowNontransitionProfile
        (omega.horizontal, eta.horizontal) j
    unfold
      sixVertexHorizontalPairRowNontransitionProfile
    rw [sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount,
      <- Finset.sum_add_distrib, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [sixVertexLocalCTypeCount,
      sixVertexLocalIncomingPattern_isCType_iff] using
        hmask.localCTypeCount (i, j)
  · change sixVertexHorizontalPairRowZeroProfile
        ((sixVertexTorusSwitchFirst mask omega eta).horizontal,
          (sixVertexTorusSwitchSecond mask omega eta).horizontal) j =
      sixVertexHorizontalPairRowZeroProfile
        (omega.horizontal, eta.horizontal) j
    exact congrFun
      (sixVertexTorusPairSwitch_rowZeroProfile mask omega eta) j


end
end StatMech.FrontierD
