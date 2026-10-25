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
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part12
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalDiscrepancyRelated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : negativeReversalGateFiber ends m j k l zero p)
    (q : positiveReversalGateFiber ends m j k l zero p) : Prop :=
  positiveReversalGateToRightMaskFiber ends m j k l zero p q ∈
    canonicalMaskRightImages ends m j k l zero p
      (negativeReversalGateToLeftMaskFiber ends m j k l zero p c)


noncomputable def canonicalDiscrepancyNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (positiveReversalGateFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ c ∈ S, CanonicalDiscrepancyRelated ends m j k l zero p c q


noncomputable def liftedNegativeReversalGateFamily
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact S.image
    (negativeReversalGateToLeftMaskFiber ends m j k l zero p)


noncomputable def canonicalNegativeFullNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) :=
  canonicalMaskRightNeighborhood ends m j k l zero p
    (liftedNegativeReversalGateFamily ends m j k l zero p S)


noncomputable def canonicalNegativePositiveNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalNegativeFullNeighborhood ends m j k l zero p S).filter
    fun q => ¬ RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero


noncomputable def canonicalNegativeCommonNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalNegativeFullNeighborhood ends m j k l zero p S).filter
    fun q => RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero


end StatMech.GrahamGHS.FourColor
