/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


noncomputable def cycleTranslateBadCount
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (base : leftMaskFiber ends m j k l zero p ×
      rightMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact #((Finset.univ : Finset
    (leftMaskFiber ends m j k l zero p)).filter fun c =>
    ¬ RowsDisconnect ends m
      (rightMaskCycleTranslate m base.1.1.1 c.1.1 base.2.1.1) k zero)


end StatMech.GrahamGHS.FourColor
