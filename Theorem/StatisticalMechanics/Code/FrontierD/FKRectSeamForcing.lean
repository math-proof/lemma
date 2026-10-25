/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeamForcing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
import Def.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectHorizontalCutEdges_card (R : FKRectTorus) :
    (fkRectHorizontalCutEdges R).card = 2 * R.width := by
  classical
  unfold fkRectHorizontalCutEdges
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod]
  · intro a b h
    exact Prod.ext (congrArg (fun x => x.1) h)
      (congrArg (fun x => x.2.1) h)

theorem fkRectVerticalCutEdges_card (R : FKRectTorus) :
    (fkRectVerticalCutEdges R).card = R.height := by
  classical
  unfold fkRectVerticalCutEdges
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg (fun x => x.2.2) h

theorem fkRectTorusCutEdges_card_le (R : FKRectTorus) :
    (fkRectTorusCutEdges R).card ≤ 2 * R.width + R.height := by
  unfold fkRectTorusCutEdges
  calc
    (fkRectHorizontalCutEdges R ∪ fkRectVerticalCutEdges R).card ≤
        (fkRectHorizontalCutEdges R).card +
          (fkRectVerticalCutEdges R).card :=
      Finset.card_union_le _ _
    _ = 2 * R.width + R.height := by
      rw [fkRectHorizontalCutEdges_card, fkRectVerticalCutEdges_card]

theorem fkRectCritical_cFE_nonneg
    {q : Real} (hq : 1 ≤ q) :
    0 ≤ StatMech.FK.cFE (fkRectCriticalP q) q :=
  (StatMech.FK.cFE_pos
    (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
    (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le

theorem fkRectCritical_cFE_le_one
    {q : Real} (hq : 1 ≤ q) :
    StatMech.FK.cFE (fkRectCriticalP q) q ≤ 1 := by
  unfold StatMech.FK.cFE
  exact (min_le_right _ _).trans
    (sub_le_self 1
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq)).le)


theorem fkRectCritical_cutClosedMass_lower
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) :
    StatMech.FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) ≤
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  calc
    StatMech.FK.cFE (fkRectCriticalP q) q ^
          (2 * R.width + R.height) ≤
        StatMech.FK.cFE (fkRectCriticalP q) q ^
          (fkRectTorusCutEdges R).card :=
      pow_le_pow_of_le_one (fkRectCritical_cFE_nonneg hq)
        (fkRectCritical_cFE_le_one hq)
        (fkRectTorusCutEdges_card_le R)
    _ ≤ fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) :=
      fkRectCritical_cFE_pow_le_closedMass R hq _


end
end StatMech.FrontierD
