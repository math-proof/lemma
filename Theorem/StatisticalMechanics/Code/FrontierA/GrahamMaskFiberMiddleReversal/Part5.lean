/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem sourceMaskCycleAction_difference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleAction ends m j k l zero p c
      (sourceMaskCycleDifference ends m j k l zero p c d) = d := by
  apply Subtype.ext
  exact balancedSwap_difference m c.1 d.1
    (congrArg Prod.fst (c.2.2.trans d.2.2.symm))
    (congrArg Prod.snd (c.2.2.trans d.2.2.symm))


theorem sourceMaskCycleAction_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    Function.Injective (sourceMaskCycleAction ends m j k l zero p c) := by
  intro z z' hzz'
  have hfun := congrArg Subtype.val hzz'
  have hmidc : middleMask m c.1 = p.1 := congrArg Prod.fst c.2.2
  have houtc : outerMask m c.1 = p.2 := congrArg Prod.snd c.2.2
  have hXc : z.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z.1.2.1
  have hXc' : z'.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z'.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z'.1.2.1
  have hYc : z.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z.2.2.1
  have hYc' : z'.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z'.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z'.2.2.1
  have hYafter : z.2.1 ⊆
      colorClass m (middleSwapOn m z.1.1 c.1) 0 ∪
        colorClass m (middleSwapOn m z.1.1 c.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have hYafter' : z'.2.1 ⊆
      colorClass m (middleSwapOn m z'.1.1 c.1) 0 ∪
        colorClass m (middleSwapOn m z'.1.1 c.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have htwo := congrArg (fun q => colorClass m q 2) hfun
  have hzero := congrArg (fun q => colorClass m q 0) hfun
  change balancedSwap m z.1.1 z.2.1 c.1 =
    balancedSwap m z'.1.1 z'.2.1 c.1 at hfun
  change colorClass m (balancedSwap m z.1.1 z.2.1 c.1) 2 =
    colorClass m (balancedSwap m z'.1.1 z'.2.1 c.1) 2 at htwo
  change colorClass m (balancedSwap m z.1.1 z.2.1 c.1) 0 =
    colorClass m (balancedSwap m z'.1.1 z'.2.1 c.1) 0 at hzero
  unfold balancedSwap at htwo hzero
  rw [colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m z.1.1 c.1 hXc,
    colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m z'.1.1 c.1 hXc'] at htwo
  rw [colorClass_outerSwapOn_zero m z.2.1 _ hYafter,
    colorClass_middleSwapOn_zero,
    colorClass_outerSwapOn_zero m z'.2.1 _ hYafter',
    colorClass_middleSwapOn_zero] at hzero
  apply Prod.ext
  · apply Subtype.ext
    exact (symmDiff_right_injective (colorClass m c.1 2)) htwo
  · apply Subtype.ext
    exact (symmDiff_right_injective (colorClass m c.1 0)) hzero


end StatMech.GrahamGHS.FourColor
