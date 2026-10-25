/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part3
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rightMaskCycleTranslate_ne
    (m : Finset I) (c d q : ↑m → Fin 4)
    (hmidcd : middleMask m c = middleMask m d)
    (houtcd : outerMask m c = outerMask m d)
    (hmidcq : middleMask m c = middleMask m q)
    (houtcq : outerMask m c = outerMask m q)
    (hcd : c ≠ d) : rightMaskCycleTranslate m c d q ≠ q := by
  intro hfixed
  let X := balancedMiddleDifference m c d
  let Y := balancedOuterDifference m c d
  have hXc : X ⊆ middleMask m c :=
    balancedMiddleDifference_subset m c d hmidcd
  have hYc : Y ⊆ outerMask m c :=
    balancedOuterDifference_subset m c d houtcd
  have hXq : X ⊆ colorClass m q 1 ∪ colorClass m q 2 := by
    rw [← middleMask, ← hmidcq]
    exact hXc
  have hYq : Y ⊆ colorClass m q 0 ∪ colorClass m q 3 := by
    rw [← outerMask, ← houtcq]
    exact hYc
  have hYq' : Y ⊆ colorClass m (middleSwapOn m X q) 0 ∪
      colorClass m (middleSwapOn m X q) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have htwo := congrArg (fun z => colorClass m z 2) hfixed
  have hthree := congrArg (fun z => colorClass m z 3) hfixed
  change balancedSwap m X Y q = q at hfixed
  change colorClass m (balancedSwap m X Y q) 2 = colorClass m q 2 at htwo
  change colorClass m (balancedSwap m X Y q) 3 = colorClass m q 3 at hthree
  unfold balancedSwap at htwo hthree
  rw [colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m X q hXq] at htwo
  rw [colorClass_outerSwapOn_three m Y _ hYq',
    colorClass_middleSwapOn_three] at hthree
  have hXempty : X = ∅ := symmDiff_eq_left.mp htwo
  have hYempty : Y = ∅ := symmDiff_eq_left.mp hthree
  apply hcd
  have hswap := balancedSwap_difference m c d hmidcd houtcd
  change balancedSwap m X Y c = d at hswap
  simpa [hXempty, hYempty, balancedSwap, middleSwapOn, outerSwapOn] using hswap


end StatMech.GrahamGHS.FourColor
