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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part8
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowClass_sourceMaskCycleAction_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (z : sourceMaskCycleSpace ends p) :
    rowClass m (sourceMaskCycleAction ends m j k l zero p c z).1 0 =
      rowClass m c.1 0 ∆ (z.1.1 ∪ z.2.1) := by
  have hmidc : middleMask m c.1 = p.1 := congrArg Prod.fst c.2.2
  have houtc : outerMask m c.1 = p.2 := congrArg Prod.snd c.2.2
  have hXc : z.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z.1.2.1
  have hYc : z.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z.2.2.1
  change rowClass m (balancedSwap m z.1.1 z.2.1 c.1) 0 = _
  exact rowClass_balancedSwap_zero hXc hYc


theorem sourceMaskCycleAction_involutive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (z : sourceMaskCycleSpace ends p)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleAction ends m j k l zero p
        (sourceMaskCycleAction ends m j k l zero p c z) z = c := by
  apply Subtype.ext
  exact balancedSwap_involutive m z.1.1 z.2.1 c.1


end StatMech.GrahamGHS.FourColor
