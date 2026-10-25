/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeGetmemRequestBound.lean -/

import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Policy.PendingLayout
import Theorem.CPythonListsort.Code.Transcription.MergeAt
import Mathlib
/-!
# `merge_getmem` call-site request bound

This module connects the actual post-trimming continuations exported by
`prepareMergeAt?` to `merge_getmem`'s exact allocation guard.  In particular,
the run-span bound comes from `PendingLayout`, and both trim bounds come from
the public gallop safety theorems applied to the concrete gallop equations in
the call-site certificate.  Neither bound is assumed by the public theorem.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Geometry of an adjacent pair selected from a valid pending layout. -/
structure PendingAdjacentPairGeometry (state : MergeState κ ν)
    (scanned : Nat) (left right : PendingRun) : Prop where
  leftBase : state.basekeys ≤ left.base
  leftNonnegative : left.len.Nonnegative
  leftPositive : 0 < left.len.toNat
  adjacent : left.endIndex = right.base
  rightNonnegative : right.len.Nonnegative
  rightPositive : 0 < right.len.toNat
  rightEnd : right.endIndex ≤ state.basekeys + scanned
  pairSpan : left.len.toNat + right.len.toNat ≤ scanned
  scannedBound : scanned ≤ state.listlen.toNat

/-- Exact facts exposed to the later `merge_lo`/`merge_hi` safety proofs. -/
structure MergeGetmemRequestBoundFacts
    (pre : MergeState κ ν) (scanned i requested : Nat)
    (call : MergeAtCall κ ν) : Prop where
  leftSelected : pre.pending[i]? = some call.left
  rightSelected : pre.pending[i + 1]? = some call.right
  storageFrame : call.state.a = pre.a
  listlenFrame : call.state.listlen = pre.listlen
  hasValuesFrame : call.state.a.hasValues = pre.a.hasValues
  allocedFrame : call.state.alloced = pre.alloced
  firstGallopBound : call.trimA.index ≤ call.left.len.toNat
  secondGallopBound : call.trimB.index ≤ call.right.len.toNat
  leftTrimAccounting :
    call.na + call.trimA.index = call.left.len.toNat
  leftTrimmed : call.na ≤ call.left.len.toNat
  rightTrimmed : call.nb ≤ call.right.len.toNat
  runLengthChain :
    call.na + call.nb ≤ call.left.len.toNat + call.right.len.toNat ∧
      call.left.len.toNat + call.right.len.toNat ≤ scanned ∧
      scanned ≤ pre.listlen.toNat
  sourceDispatch :
    (requested = call.na ∧ call.na ≤ call.nb) ∨
      (requested = call.nb ∧ call.nb < call.na)
  requestIsMinimum : requested = min call.na call.nb
  requestRoundtrip : (BitVec.ofNat 64 requested).toNat = requested
  requestNonnegative : PySSize.Nonnegative (BitVec.ofNat 64 requested)
  smallerHalfChain :
    requested ≤ (call.na + call.nb) / 2 ∧
      (call.na + call.nb) / 2 ≤ pre.listlen.toNat / 2
  requestWordHalfChain :
    (BitVec.ofNat 64 requested).toNat ≤ (call.na + call.nb) / 2 ∧
      (call.na + call.nb) / 2 ≤ pre.listlen.toNat / 2
  keyedLimit : call.state.a.hasValues = true →
    mergeGetmemAllocationLimit call.state.a =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2 ^ 59 - 1
  unkeyedLimit : call.state.a.hasValues = false →
    mergeGetmemAllocationLimit call.state.a =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2 ^ 60 - 1
  requestWithinLimit :
    (BitVec.ofNat 64 requested).toNat ≤
      mergeGetmemAllocationLimit call.state.a
  guardNotRejected :
    (mergeGetmem call.state (BitVec.ofNat 64 requested)).outcome ≠
      .guardRejected

/-- Cursor and extent facts needed by the two merge evaluators.  This
certificate is deliberately downstream of the actual `prepareMergeAt?`
continuation: positivity, adjacency, representability, and the complete main
range are conclusions, not independent call-site assumptions. -/
structure MergeAtSafetyGeometry
    (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν) : Prop where
  evidence : MergeAtCallsiteEvidence pre i call
  ssaNonnegative : 0 ≤ call.ssa
  ssbNonnegative : 0 ≤ call.ssb
  adjacent : call.ssa + Int.ofNat call.na = call.ssb
  mergedRange :
    call.ssa + Int.ofNat (call.na + call.nb) ≤
      Int.ofNat call.state.data.entries.size
  rightRange :
    call.ssb + Int.ofNat call.nb ≤
      Int.ofNat call.state.data.entries.size
  leftPositive : 0 < call.na
  rightPositive : 0 < call.nb
  leftWordBound : call.na ≤ PY_SSIZE_T_MAX
  rightWordBound : call.nb ≤ PY_SSIZE_T_MAX
  runLengthBound : call.na + call.nb ≤ pre.listlen.toNat

/-- Aggregate roadmap contract for both source dispatch branches. -/
structure MergeGetmemRequestBoundContract (κ : Type u) (ν : Type v) : Prop where
  mergeLo : ∀ (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν),
    PendingLayout pre scanned →
    pre.listlen.toNat ≤ PY_LIST_MAX →
    prepareMergeAt? pre i = some (.mergeLo call) →
    MergeGetmemRequestBoundFacts pre scanned i call.na call
  mergeHi : ∀ (pre : MergeState κ ν) (scanned i : Nat) (call : MergeAtCall κ ν),
    PendingLayout pre scanned →
    pre.listlen.toNat ≤ PY_LIST_MAX →
    prepareMergeAt? pre i = some (.mergeHi call) →
    MergeGetmemRequestBoundFacts pre scanned i call.nb call
  keyedFencepost : ∀ (state : MergeState κ ν),
    state.a.hasValues = true →
    (((2 ^ 59 - 1 : Nat) : PySSize).sle state.alloced) = false →
    mergeGetmemAllocationLimit state.a = 2 ^ 59 - 1 ∧
      (mergeGetmem state ((2 ^ 59 - 1 : Nat) : PySSize)).outcome = .grown ∧
      (mergeGetmem state ((2 ^ 59 : Nat) : PySSize)).outcome = .guardRejected

end CPythonListsort
