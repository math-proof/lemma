/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part4
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem exists_rightMaskFiber_pair_of_cycleTranslate_disconnects
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero) :
    ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r := by
  let r := rightMaskCycleTranslateMemOfDisconnects
    ends m j k l zero p c d q hdisc
  have hcd' : c.1.1 ≠ d.1.1 := by
    intro heq
    apply hcd
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hprofilecd : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m d.1.1 := c.2.trans d.2.symm
  have hprofilecq : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m q.1.1 := c.2.trans q.2.symm
  have hne : rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1 ≠ q.1.1 :=
    rightMaskCycleTranslate_ne m c.1.1 d.1.1 q.1.1
      (congrArg Prod.fst hprofilecd) (congrArg Prod.snd hprofilecd)
      (congrArg Prod.fst hprofilecq) (congrArg Prod.snd hprofilecq) hcd'
  refine ⟨q, r, ?_⟩
  intro hqr
  apply hne
  exact (congrArg (fun z : rightMaskFiber ends m j k l zero p => z.1.1) hqr).symm


end StatMech.GrahamGHS.FourColor
