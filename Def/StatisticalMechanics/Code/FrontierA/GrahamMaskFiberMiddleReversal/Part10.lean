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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part7
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def leftMaskFiberEquivSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ≃
      leftSourceMaskGateFiber ends m j k l zero p where
  toFun c := ⟨leftMaskFiberToSourceMaskFiber
      ends m j k l zero p c, c.1.2.2.2.2.2⟩
  invFun c := ⟨⟨c.1.1, ⟨c.1.2.1.1, c.1.2.1.2.1,
      c.1.2.1.2.2.1, c.1.2.1.2.2.2, c.2⟩⟩, c.1.2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl


noncomputable def rightMaskFiberEquivReversedSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    rightMaskFiber ends m j k l zero p ≃
      reversedRightSourceMaskGateFiber ends m j k l zero p where
  toFun q := ⟨⟨middleSwap m q.1.1, ⟨
      (leftSourcePattern_middleSwap_iff_rightSourcePattern
        ends m {j, k} {k, l} q.1.1).2
          ⟨q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2.1⟩,
      (fourColorMaskProfile_middleSwap m q.1.1).trans q.2⟩⟩, by
    simpa only [middleSwap_involutive] using q.1.2.2.2.2.2⟩
  invFun c := by
    have hs : RightSourcePattern ends m {j, k} {k, l}
        (middleSwap m c.1.1) :=
      (rightSourcePattern_middleSwap_iff_leftSourcePattern
        ends m {j, k} {k, l} c.1.1).2 c.1.2.1
    exact ⟨⟨middleSwap m c.1.1,
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, c.2⟩⟩,
      (fourColorMaskProfile_middleSwap m c.1.1).trans c.1.2.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact middleSwap_involutive m q.1.1
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact middleSwap_involutive m c.1.1


def sourceMaskGatePointToLeftMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    leftMaskFiber ends m j k l zero p :=
  ⟨⟨c.1, ⟨c.2.1.1, c.2.1.2.1, c.2.1.2.2.1,
    c.2.1.2.2.2, hdisc⟩⟩, c.2.2⟩


noncomputable def canonicalReferenceReturnRaw
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : ↑m -> Fin 4 :=
  middleSwap m
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero) c)


end StatMech.GrahamGHS.FourColor
