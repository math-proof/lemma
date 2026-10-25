/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


theorem rightMaskCycleTranslate_disconnects_of_respectsCuts
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hcuts : RightMaskCycleDifferenceRespectsCuts ends m
      (rowClass m q 0) (rightMaskCycleDifference m a c) k) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero := by
  have hrows := rightMaskCycleTranslate_rows m a c q hac haq
  rw [RowsDisconnect] at hq ⊢
  rw [hrows.1, hrows.2]
  constructor
  · exact not_conn_symmDiff_of_noCrossing_componentComplement
      ends (rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.1 hcuts.1
  · rw [rowClass_one_eq_sdiff] at hq ⊢
    exact not_conn_symmDiff_of_noCrossing_componentComplement
      ends (m \ rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.2 hcuts.2


end StatMech.GrahamGHS.FourColor
