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
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part22
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawSelfBase_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p)) :
    CanonicalRawGateRelated ends m j k l zero p c.1
      (canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c) := by
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let q := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  have hright : RowsDisconnect ends m
      (middleSwap m
        (canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c).1) k zero := by
    exact canonicalSelfPulledSourcePoint_rightGate ends m j k l zero
      hloop hjk hkl hk0 p c.1 hc
  refine ⟨hc, hright, ?_⟩
  have hqmem : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    rw [mem_canonicalMaskRightImages_iff]
    refine ⟨a, canonicalTransferWorks_self hloop hjk hkl hk0 a, ?_⟩
    rfl
  have heq :
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p).symm
          ⟨canonicalStableRawSelfBase ends m j k l zero
            hloop hjk hkl hk0 p c, hright⟩ = q := by
    let e := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p
    calc
      e.symm ⟨canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c, hright⟩ = e.symm (e q) := by
        congr 1
      _ = q := e.symm_apply_apply q
  simpa only [a, q, heq] using hqmem


end StatMech.GrahamGHS.FourColor
