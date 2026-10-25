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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def sourceMaskMiddleReversalEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftSourceMaskFiber ends m j k l zero p ≃
      rightSourceMaskFiber ends m j k l zero p where
  toFun c := ⟨middleSwap m c.1, ⟨
    (rightSourcePattern_middleSwap_iff_leftSourcePattern
      ends m {j, k} {k, l} c.1).2 c.2.1,
    (fourColorMaskProfile_middleSwap m c.1).trans c.2.2⟩⟩
  invFun c := ⟨middleSwap m c.1, ⟨
    (leftSourcePattern_middleSwap_iff_rightSourcePattern
      ends m {j, k} {k, l} c.1).2 c.2.1,
    (fourColorMaskProfile_middleSwap m c.1).trans c.2.2⟩⟩
  left_inv c := by
    apply Subtype.ext
    exact middleSwap_involutive m c.1
  right_inv c := by
    apply Subtype.ext
    exact middleSwap_involutive m c.1


end StatMech.GrahamGHS.FourColor
