/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part17
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawReferenceAlternateData_target_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r)
    (hbase : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r) :
    (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbase).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p r c hcr.symm hbase.symm).target := by
  classical
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let hr := canonicalRawCommonClosure_leftGate
    ends m j k l zero p r.1 r.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let ref := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p r.1 hr
  have haref : a ≠ ref := by
    intro h
    apply hcr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : leftMaskFiber ends m j k l zero p => q.1.1) h
  let qa := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  let qref := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p r.1 hr
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  have hselfEq : qa = qref := by
    apply e.injective
    apply Subtype.ext
    exact hbase
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p a a
          (canonicalTransferWorks_self hloop hjk hkl hk0 a)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p ref ref
            (canonicalTransferWorks_self hloop hjk hkl hk0 ref)).1.1 := by
    exact congrArg (fun q : rightMaskFiber ends m j k l zero p => q.1.1)
      hselfEq
  let hworksRA := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).1
  let hworksAR := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).2
  let altRA := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p ref a hworksRA
  let altAR := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p a ref hworksAR
  have htranslated : canonicalTranslatedRow ends m k zero a.1.1 a.1.1 =
      canonicalTranslatedRow ends m k zero ref.1.1 ref.1.1 := by
    have hrow := congrArg (fun q => rowClass m q 0) himage
    have harow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a a
        (canonicalTransferWorks_self hloop hjk hkl hk0 a)
    have hrefrow := rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p ref ref
        (canonicalTransferWorks_self hloop hjk hkl hk0 ref)
    exact harow.symm.trans (hrow.trans hrefrow)
  have hopposite := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 ref.1.1 a.1.1 ref.1.1 htranslated
  have hraw : altRA.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) ref.1.1 := by
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl ref a a ref).mpr hopposite
  have halt : altRA = altAR := by
    apply Subtype.ext
    apply Subtype.ext
    exact hraw
  unfold canonicalStableRawReferenceAlternateData
  dsimp only
  exact congrArg (fun q : rightMaskFiber ends m j k l zero p => (e q).1) halt


theorem canonicalStableRawReferenceAlternateData_target_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d r : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r) (hdr : d ≠ r)
    (hbasec : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (hbased : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d r hdr hbased).target) :
    c = d := by
  classical
  unfold canonicalStableRawReferenceAlternateData at htarget
  dsimp only at htarget
  have hright := (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).injective (Subtype.ext htarget)
  have hraw := congrArg
    (fun q : rightMaskFiber ends m j k l zero p => q.1.1) hright
  change balancedSwap m
      (canonicalMiddleTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (canonicalOuterTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p c.1 c.2)).1.1 =
    balancedSwap m
      (canonicalMiddleTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (canonicalOuterTransfer ends m
        (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
          (canonicalRawCommonClosure_leftGate
            ends m j k l zero p r.1 r.2)).1.1 k zero)
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p d.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p d.1 d.2)).1.1 at hraw
  have hinv := congrArg (balancedSwap m
    (canonicalMiddleTransfer ends m
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)).1.1 k zero)
    (canonicalOuterTransfer ends m
      (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p r.1
        (canonicalRawCommonClosure_leftGate
          ends m j k l zero p r.1 r.2)).1.1 k zero)) hraw
  simp only [balancedSwap_involutive] at hinv
  apply Subtype.ext
  apply Subtype.ext
  exact hinv


theorem canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d r q : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hcr : c ≠ r) (hdq : d ≠ q)
    (hbasec : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p r)
    (hbased : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p d =
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p q)
    (hrq : r = q)
    (htarget : (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target =
      (canonicalStableRawReferenceAlternateData
        ends m j k l zero hloop hjk hkl hk0 p d q hdq hbased).target) :
    c = d := by
  subst q
  exact canonicalStableRawReferenceAlternateData_target_injective
    ends m j k l zero hloop hjk hkl hk0 p c d r
      hcr hdq hbasec hbased htarget


end StatMech.GrahamGHS.FourColor
