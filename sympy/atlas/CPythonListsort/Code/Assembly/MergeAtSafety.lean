/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeMemoryLifecycle
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation

/-!
# `merge_at` safety

This module instruments the pending-stack updates and the two trimming gallops
performed by `merge_at`, then delegates the selected merge continuation to the
already traced `merge_lo` or `merge_hi` evaluator.  The logical shrink of the
active pending array is not an indexed C access; the indexed reads and writes
which precede it are recorded in source order.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Convert a traced `merge_lo` result to the common `merge_at` result. -/
private def mergeAtFromLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Convert a traced `merge_hi` result to the common `merge_at` result. -/
private def mergeAtFromHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

private def mergeAtSuccessResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

private def mergeAtOutOfFuelResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

/-- The logical pending-stack splice performed by `merge_at`.  The traced
implementation below proves that its physical write sequence computes this
state. -/
private def mergeAtCombinedState (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  { state with
    pending :=
      (state.pending.setIfInBounds i
        { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) }

/-- Trace the C-level pending writes which install the combined run and, on the
third-last branch, slide the uninvolved last run down one slot.  The returned
state uses the reviewed transcription's single logical splice; the preceding
typed operations establish and record the corresponding physical accesses.
-/
def mergeAtPendingUpdateTraced? (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : TraceResult (MergeState κ ν) :=
  let combined : PendingRun := { left with len := left.len + right.len }
  let updated :=
    (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).bind fun written =>
      if i + 3 = state.pending.size then
        (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))).bind fun last =>
          (TraceResult.pendingRunWrite? written (Int.ofNat (i + 1)) last).map
            (fun slid =>
              { slid with pending := slid.pending.eraseIdxIfInBounds (i + 2) })
      else
        TraceResult.pure
          { written with pending := written.pending.eraseIdxIfInBounds (i + 1) }
  updated.recordSuccessPolicyEvent fun _ =>
    .merge
      { index := i
        left := RunSpan.ofPendingRun left
        right := RunSpan.ofPendingRun right }

private def mergeAtAfterTrimBTraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB lastA : SortSliceEntry κ ν)
    (trimA trimB : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimB.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if right.len.toNat < trimB.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    let nb := trimB.index
    if nb = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else if na ≤ nb then
      TraceResult.pure (.mergeLo
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })
    else
      TraceResult.pure (.mergeHi
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })

private def mergeAtAfterTrimATraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB : SortSliceEntry κ ν)
    (trimA : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimA.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if left.len.toNat < trimA.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    if na = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else
      (TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat (ssa + na - 1))).bind fun lastA =>
        (gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
          mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB

private structure MergeAtTailSafetyPost (call : MergeState κ ν)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  stateEq : prepared.state = call

/-- Traced prefix of `merge_at`: pending-stack selection and mutation, both
endpoint reads, both trimming gallops, and the final dispatch decision. -/
def prepareMergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtPreparation κ ν) :=
  if 2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) then
    (TraceResult.pendingRunRead? state (Int.ofNat i)).bind fun left =>
      (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).bind fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          (mergeAtPendingUpdateTraced? state i left right).bind fun call =>
            (TraceResult.sortSliceKeysRead? call.data
              (Int.ofNat right.base)).bind fun firstB =>
              (gallopRightTraced? call
                (.main call.data (Int.ofNat left.base)) firstB.key
                left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB trimA
        else
          TraceResult.failure
  else
    TraceResult.failure

/-- The exact source-order trace prefix on a preparation path which reaches a
merge continuation.  The first gallop's result determines the last-A endpoint
read used to start the second gallop. -/
def mergeAtPreparationDispatchTrace (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : AccessTrace :=
  (TraceResult.pendingRunRead? pre (Int.ofNat i)).trace.compose
    ((TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).trace.compose
      ((mergeAtPendingUpdateTraced? pre i call.left call.right).trace.compose
        ((TraceResult.sortSliceKeysRead? call.state.data
          (Int.ofNat call.right.base)).trace.compose
          ((gallopRightTraced? call.state
            (.main call.state.data (Int.ofNat call.left.base)) call.firstB.key
            call.left.len.toNat 0).trace.compose
            ((TraceResult.sortSliceKeysRead? call.state.data
              (Int.ofNat (call.left.base + call.trimA.index + call.na - 1))).trace.compose
              (gallopLeftTraced? call.state
                (.main call.state.data (Int.ofNat call.right.base)) call.lastA.key
                call.right.len.toNat (call.right.len.toNat - 1)).trace)))))

set_option maxHeartbeats 5000000 in
-- The proof follows every nested bind and early-return guard in both dispatch branches.
set_option linter.flexible false in

/-- State fields which `merge_at` is forbidden to mutate.  The pending stack,
main data contents, temporary allocation, and adaptive `min_gallop` output are
intentionally absent because the operation may change them. -/
structure MergeAtStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeAtStableFrame

/-- Safety facts at the boundary between `merge_at`'s trimming prefix and its
selected merge continuation. -/
structure MergeAtPreparationSafetyPost (pre : MergeState κ ν) (i : Nat)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = prepareMergeAt? pre i
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  tempInvariant : TempStorageInv prepared.state.a prepared.state.alloced
  tempLive : prepared.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant prepared.state.a.hasValues prepared.state.data
  hasValuesFrame : prepared.state.a.hasValues = pre.a.hasValues
  storageFrame : prepared.state.a = pre.a
  allocedFrame : prepared.state.alloced = pre.alloced
  dataFrame : prepared.state.data = pre.data
  stableFrame : MergeAtStableFrame pre prepared.state

/-- Execute the traced merge continuation selected by
`prepareMergeAtTraced?`.  A successful directional continuation appends
exactly one raw call record computed from its actual result. -/
def finishMergeAtPreparationTraced? :
    MergeAtPreparation κ ν → TraceResult (MergeAtResult κ ν)
  | .finished result => TraceResult.pure result
  | .mergeLo call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeLoMemoryCallEvent call result))).map
        mergeAtFromLo
  | .mergeHi call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeHiMemoryCallEvent call result))).map
        mergeAtFromHi

/-- Fully traced `merge_at` evaluator. -/
def mergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtResult κ ν) :=
  (prepareMergeAtTraced? state i).bind finishMergeAtPreparationTraced?

/-- Full public postcondition for a source-admitted `merge_at` call. -/
structure MergeAtSafetyPost (pre : MergeState κ ν) (scanned i : Nat)
    (execution : TraceResult (MergeAtResult κ ν))
    (result : MergeAtResult κ ν) : Prop where
  resultEq : execution.result = some result
  returnCode : result.returnCode = 0
  resultFuel : result.fuelExhausted = false
  traceFuel : execution.trace.fuelExhausted = false
  accessesInBounds : execution.trace.allAccessesInBounds
  tempAccessesLive : execution.trace.tempPayloadAccessesLive
  noPushes : execution.trace.pushDepths = []
  /-- Every raw lifecycle observation emitted by this `merge_at` invocation is
  validated in the values mode inherited from its caller. -/
  memoryEventsValid : execution.trace.memoryEventsValid pre.a.hasValues
  /-- `merge_at` owns directional call records only; initialization and final
  cleanup remain top-level events. -/
  onlyMergeMemoryEvents : execution.trace.onlyMergeMemoryEvents
  /-- The initialized physical-slot ceiling is threaded through every call
  record rather than reconstructed from raw observations. -/
  memoryEventsBounded :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      execution.trace.mergeMemoryEventsBounded
  /-- Exact local event cardinality: an early trimmed exit emits nothing and a
  completed directional merge emits exactly its one call record. -/
  memoryEventShape :
    execution.trace.memoryEvents = [] ∨
      ∃ call, execution.trace.memoryEvents = [.mergeCall call]
  /-- The call records are not merely well-shaped: their concrete storage
  boundaries form one gap-free path from the caller state to the result. -/
  memorySegment : execution.trace.MergeMemorySegment
    (MergeMemorySnapshot.ofState pre)
    (MergeMemorySnapshot.ofState result.state)
  exactErasure : execution.erase = mergeAt? pre i
  tempInvariant : TempStorageInv result.state.a result.state.alloced
  tempLive : result.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant result.state.a.hasValues result.state.data
  hasValuesFrame : result.state.a.hasValues = pre.a.hasValues
  stableFrame : MergeAtStableFrame pre result.state
  pendingLayout : PendingLayout result.state scanned
  /-- The successful full call emits exactly one logical merge event for the
  two selected adjacent runs as they stood before trimming, and the result
  pending array is exactly their source-level splice. -/
  logicalMerge : ∃ left right,
    pre.pending[i]? = some left ∧
      pre.pending[i + 1]? = some right ∧
      result.state.pending =
        (pre.pending.setIfInBounds i
          { left with len := left.len + right.len }).eraseIdxIfInBounds
            (i + 1) ∧
      execution.trace.policyEvents =
        [.merge
          { index := i
            left := RunSpan.ofPendingRun left
            right := RunSpan.ofPendingRun right }]
  physicalSlotsBound :
    (MergeMemorySnapshot.ofState pre).PhysicalBound →
      (MergeMemorySnapshot.ofState result.state).PhysicalBound

/-! ## Logical-event anti-vacuity regression -/

private def mergeAtPolicyEarlyTrimLeft : PendingRun :=
  { base := 0, len := 1, power := some 4 }

private def mergeAtPolicyEarlyTrimRight : PendingRun :=
  { base := 1, len := 1, power := some 7 }

private def mergeAtPolicyEarlyTrimTail : PendingRun :=
  { base := 2, len := 1, power := none }

private def mergeAtPolicyEarlyTrimState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending :=
      #[mergeAtPolicyEarlyTrimLeft,
        mergeAtPolicyEarlyTrimRight,
        mergeAtPolicyEarlyTrimTail]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def mergeAtPolicyEarlyTrimCall : MergeState Nat Nat :=
  mergeAtCombinedState mergeAtPolicyEarlyTrimState 0
    mergeAtPolicyEarlyTrimLeft mergeAtPolicyEarlyTrimRight

private def mergeAtFinishedSuccessShape
    (prepared : MergeAtPreparation Nat Nat) : Option (Int × Bool) :=
  match prepared with
  | .finished result => some (result.returnCode, result.fuelExhausted)
  | .mergeLo _ | .mergeHi _ => none
