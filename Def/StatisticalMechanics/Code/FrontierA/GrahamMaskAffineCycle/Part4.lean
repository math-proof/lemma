/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part4
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def rightMaskCycleTranslateMemOfDisconnects
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero) :
    rightMaskFiber ends m j k l zero p := by
  let X := balancedMiddleDifference m c.1.1 d.1.1
  let Y := balancedOuterDifference m c.1.1 d.1.1
  have hprofilecd : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m d.1.1 := c.2.trans d.2.symm
  have hprofilecq : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m q.1.1 := c.2.trans q.2.symm
  have hmidcd : middleMask m c.1.1 = middleMask m d.1.1 :=
    congrArg Prod.fst hprofilecd
  have houtcd : outerMask m c.1.1 = outerMask m d.1.1 :=
    congrArg Prod.snd hprofilecd
  have hmidcq : middleMask m c.1.1 = middleMask m q.1.1 :=
    congrArg Prod.fst hprofilecq
  have houtcq : outerMask m c.1.1 = outerMask m q.1.1 :=
    congrArg Prod.snd hprofilecq
  have hXc : X ⊆ middleMask m c.1.1 :=
    balancedMiddleDifference_subset m c.1.1 d.1.1 hmidcd
  have hYc : Y ⊆ outerMask m c.1.1 :=
    balancedOuterDifference_subset m c.1.1 d.1.1 houtcd
  have hXq : X ⊆ colorClass m q.1.1 1 ∪ colorClass m q.1.1 2 := by
    rw [← middleMask, ← hmidcq]
    exact hXc
  have hYq : Y ⊆ colorClass m q.1.1 0 ∪ colorClass m q.1.1 3 := by
    rw [← outerMask, ← houtcq]
    exact hYc
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.1.2.2.1, d.1.2.2.1]
    simp
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.1.2.1, d.1.2.1]
    simp
  have hright : RightPattern ends m {j, k} {k, l} k zero
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) := by
    apply rightPattern_of_sourceless_balancedSwap q.1.2 hXq hYq
      hsrcX hsrcY
    simpa only [rightMaskCycleTranslate, X, Y] using hdisc
  refine ⟨⟨rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1, hright⟩, ?_⟩
  calc
    fourColorMaskProfile m
        (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) =
        fourColorMaskProfile m q.1.1 := by
      simp [fourColorMaskProfile, rightMaskCycleTranslate,
        middleMask_balancedSwap, outerMask_balancedSwap]
    _ = p := q.2


end StatMech.GrahamGHS.FourColor
