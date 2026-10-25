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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part11
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalSelfPulledSourcePoint_val_eq_referenceReturn
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hdisc).1 =
      canonicalReferenceReturnRaw ends m k zero c.1 c.1 := by
  rfl


theorem canonicalSelfPulledSourcePoint_reference_fails_of_negative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hneg : ReversalGateNegative ends m j k l zero p c) :
    ¬ CanonicalTransferWorks ends m k zero c.1
      (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hneg.1).1 := by
  rw [canonicalSelfPulledSourcePoint_val_eq_referenceReturn]
  unfold canonicalReferenceReturnRaw
  exact ((canonicalTransferWorks_oppositeReturn_iff
    ends m k zero c.1 c.1).not.mpr hneg.2)


theorem canonicalSelfPulledSourcePoint_rightGate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    RowsDisconnect ends m
      (middleSwap m (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hdisc).1) k zero :=
  (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p
    (canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p c hdisc)).2


end StatMech.GrahamGHS.FourColor
