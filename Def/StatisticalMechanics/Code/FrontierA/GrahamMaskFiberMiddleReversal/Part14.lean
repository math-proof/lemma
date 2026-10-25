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
import Instance.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def negativeReversalGateToLeftMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    negativeReversalGateFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p := fun c =>
  sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 c.2.1


noncomputable def positiveReversalGateToRightMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    positiveReversalGateFiber ends m j k l zero p ->
      rightMaskFiber ends m j k l zero p := fun c =>
  (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).symm ⟨c.1, c.2.2⟩


def CanonicalRawGateRelated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) : Prop :=
  ∃ (hc : RowsDisconnect ends m c.1 k zero)
      (hd : RowsDisconnect ends m (middleSwap m d.1) k zero),
    (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d, hd⟩ ∈
      canonicalMaskRightImages ends m j k l zero p
        (sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p c hc)


noncomputable def canonicalRawNegativeGateFinset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Finset (leftSourceMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun c =>
    ReversalGateNegative ends m j k l zero p c

noncomputable def canonicalRawCommonClosureIter
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Nat ->
      Finset (leftSourceMaskFiber ends m j k l zero p) :=
  StatMech.FrontierA.finiteCommonClosureIter
    (fun c => RowsDisconnect ends m c.1 k zero)
    (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawNegativeGateFinset ends m j k l zero p)

end StatMech.GrahamGHS.FourColor
