/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawReferenceAlternateData
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
    CanonicalStableRawReferenceAlternateData
      ends m j k l zero hloop hjk hkl hk0 p c r := by
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
    intro har
    apply hcr
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : leftMaskFiber ends m j k l zero p => x.1.1) har
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
  let hworks := (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p a ref himage).1
  let alt := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p ref a hworks
  have hcommon := canonicalSelfImageFiber_referenceTransfer_common_ne_self
    ends m j k l zero hloop hjk hkl hk0 p a ref haref himage
  let raw := (e alt).1
  have hsourceRelated : CanonicalRawGateRelated
      ends m j k l zero p c.1 raw := by
    refine ⟨hc, (e alt).2, ?_⟩
    have hback : e.symm ⟨raw, (e alt).2⟩ = alt := by
      exact e.symm_apply_apply alt
    rw [hback]
    exact hcommon.1
  have hrefRelated : CanonicalRawGateRelated
      ends m j k l zero p r.1 raw := by
    refine ⟨hr, (e alt).2, ?_⟩
    have hback : e.symm ⟨raw, (e alt).2⟩ = alt := by
      exact e.symm_apply_apply alt
    rw [hback]
    exact hcommon.2.1
  have hrawNe : raw ≠ canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p r := by
    intro hraw
    apply hcommon.2.2
    let self := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a a
        (canonicalTransferWorks_self hloop hjk hkl hk0 a)
    apply e.injective
    apply Subtype.ext
    change raw = (e self).1
    exact hraw.trans hbase.symm
  exact ⟨raw, hsourceRelated, hrefRelated, hrawNe⟩


end StatMech.GrahamGHS.FourColor
