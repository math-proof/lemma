/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Theorem.CPythonListsort.Code.Assembly.AccessTrace.Part2
/-!
# Compositional access and pending-push traces

This module provides the trace carrier used by the comparator-independent
safety layer.  An access event describes an *attempt*: instrumentation emits
the event before consulting the modeled array, so an invalid access is retained
in the trace even when the local evaluator returns `none`.  Temporary payload
events carry the backing state observed at that same point.  Reads of
`TempStorage.hasValues` and `MergeState.alloced` are metadata reads, not payload
events, and therefore do not use the temporary-payload region.

Local instrumented evaluators return `TraceResult`s.  `TraceResult.bind`
concatenates their local traces in execution order and preserves the trace of a
failed operation.  The later top-level instrumented evaluator must be assembled
from those local evaluators; wrapping the existing evaluator in an empty trace
would not satisfy this interface's intended use.

Pending pushes are deliberately separate from ordinary indexed accesses.  The
wrapper below performs the existing unconditional `Array.push` first and then
records its resulting depth.  There is no capacity guard, refusal result,
clamping operation, or assertion-failure event in this trace model.
-/


namespace CPythonListsort

universe u v w

namespace AccessTrace

namespace TraceResult

/-- Low-level attachment of one access-attempt event to an already-computed
modeled result.  The event is present whether `result` is `some` or `none`.
Callers should normally use one of the state-derived access wrappers below. -/
def captureAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) (result : Option α) : TraceResult α :=
  { result := result
    trace := AccessTrace.singletonAccess kind region index extent }

/-- Low-level array-read instrumenter shared by the region-specific wrappers.
Negative and past-the-end attempts return `none` only after their event has
been formed.  Callers should not supply ad-hoc labels for listsort storage. -/
def arrayRead? (region : AccessRegion) (array : Array α)
    (index : Int) : TraceResult α :=
  let result :=
    if 0 ≤ index then
      array[index.toNat]?
    else
      none
  captureAccess .read region index array.size result

/-- Low-level array-write instrumenter shared by the region-specific wrappers.
Rejected writes leave the source array untouched by returning `none`, while
retaining the event.  Callers should not supply ad-hoc labels for listsort
storage. -/
def arrayWrite? (region : AccessRegion) (array : Array α)
    (index : Int) (value : α) : TraceResult (Array α) :=
  let result :=
    if 0 ≤ index ∧ index.toNat < array.size then
      some (array.setIfInBounds index.toNat value)
    else
      none
  captureAccess .write region index array.size result

/-- Mark a local result as fuel-exhausted without disturbing prior events. -/
def markFuelExhausted (current : TraceResult α) : TraceResult α :=
  { current with trace := current.trace.compose AccessTrace.exhausted }

/-- Read one initialized temporary payload cell.  Both the region's backing
and its extent come from `storage` at the attempt.  An in-bounds but
uninitialized (`none`) cell rejects the read only after preserving that event. -/
def tempPayloadRead? (storage : TempStorage κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  (arrayRead? (.tempPayload storage.backing) storage.cells index).bind fun cell =>
    match cell with
    | none => failure
    | some entry => pure entry

/-- Initialize or replace one temporary payload cell.  The event derives its
backing and extent from the pre-write storage even when the write is rejected. -/
def tempPayloadWrite? (storage : TempStorage κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (TempStorage κ ν) :=
  (arrayWrite? (.tempPayload storage.backing) storage.cells index (some entry)).map
    fun cells => { storage with cells := cells }

/-- Instrument a key-array read from the paired `SortSlice` representation.
The returned entry carries the synchronized payload so a caller can reproduce
the uninstrumented atomic representation, but this event records only the key
component. -/
def sortSliceKeysRead? (slice : SortSlice κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  captureAccess .read .inputKeys index slice.entries.size (slice.read? index)

/-- Instrument a synchronized-values read.  Call this only on paths on which
the C `values` pointer is present; the extent is always derived from `slice`. -/
def sortSliceValuesRead? (slice : SortSlice κ ν) (index : Int) :
    TraceResult (SortSliceEntry κ ν) :=
  captureAccess .read .synchronizedValues index slice.entries.size
    (slice.read? index)

/-- Instrument a key-array write through the exact `SortSlice.write?` result. -/
def sortSliceKeysWrite? (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  captureAccess .write .inputKeys index slice.entries.size
    (slice.write? index entry)

/-- Instrument a synchronized-values write through the exact
`SortSlice.write?` result.  Call this only when the values array is present. -/
def sortSliceValuesWrite? (slice : SortSlice κ ν) (index : Int)
    (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  captureAccess .write .synchronizedValues index slice.entries.size
    (slice.write? index entry)

/-- Read an indexed pending run from the current state.  Pushes use the
separate post-push-depth channel and never call this wrapper. -/
def pendingRunRead? (state : MergeState κ ν) (index : Int) :
    TraceResult PendingRun :=
  arrayRead? .pendingRuns state.pending index

/-- Replace an indexed pending run in the current state.  The event's extent
is the pending-array size before the attempted update. -/
def pendingRunWrite? (state : MergeState κ ν) (index : Int)
    (run : PendingRun) : TraceResult (MergeState κ ν) :=
  (arrayWrite? .pendingRuns state.pending index run).map fun pending =>
    { state with pending := pending }

/-- Update only the stored power field of one pending run while recording the
single indexed write performed by C.  Looking up the other fields is part of
constructing the replacement record, not a second source-level read event.
Rejected negative and out-of-range writes retain their attempted event. -/
def pendingRunPowerWrite? (state : MergeState κ ν) (index : Int)
    (power : Nat) : TraceResult (MergeState κ ν) :=
  let result :=
    if 0 ≤ index then
      state.pending[index.toNat]?.map fun top =>
        { state with
          pending := state.pending.setIfInBounds index.toNat
            ({ top with power := some power } : PendingRun) }
    else
      none
  captureAccess .write .pendingRuns index state.pending.size result

/-- Instrument the unconditional pending-run push.  The state update is the
same unbounded `Array.push` used by `list_sort_impl`; keeping this core wrapper
dependent only on `MergeState` lets every local transcribed evaluator import
the trace API without a dependency cycle.

This low-level compatibility wrapper records only the post-push depth because
it is not given run-discovery or adaptive-minrun metadata.  The real scan loop
must use `pushFormedRunTraced` below when it records a formed leaf. -/
def pushPendingRunTraced (state : MergeState κ ν) (run : PendingRun) :
    TraceResult (MergeState κ ν) :=
  let pushed := { state with pending := state.pending.push run }
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.pending.size }

/-- Push a run formed by the scan loop and retain the adaptive-minrun context
needed to interpret that leaf later.  The run and depth are derived rather
than accepted as metadata, preventing those two fields from disagreeing with
the actual state transition. -/
def pushFormedRunTraced (state : MergeState κ ν) (run : PendingRun)
    (naturalLength target remainingBefore : Nat) :
    TraceResult (MergeState κ ν) :=
  let pushed := { state with pending := state.pending.push run }
  let event : PendingPushEvent :=
    { run := RunSpan.ofPendingRun run
      depthAfter := pushed.pending.size
      naturalLength := naturalLength
      target := target
      remainingBefore := remainingBefore }
  { result := some pushed
    trace := AccessTrace.singletonFormedRun event }

/-! ## Executable regressions -/

def accessTraceRegressionRun : PendingRun :=
  { base := 0, len := 1, power := none }

/-- A concrete pending array at the C capacity, used only to demonstrate the
trace semantics without requiring an otherwise irrelevant `MergeState`. -/
def accessTraceCapacityPending : Array PendingRun :=
  Array.replicate MAX_MERGE_PENDING accessTraceRegressionRun

/-- The same total push performed by `pushPendingRunTraced`, projected to the
pending array for a closed executable capacity regression. -/
def accessTraceForcedPush : TraceResult (Array PendingRun) :=
  let pushed := accessTraceCapacityPending.push accessTraceRegressionRun
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.size }

def releasedTempStorage : TempStorage Nat Nat :=
  { cells := #[]
    backing := .released
    hasValues := true }

def rejectedReleasedTempRead : TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? releasedTempStorage 0

def uninitializedTempStorage : TempStorage Nat Nat :=
  { cells := #[none]
    backing := .inline
    hasValues := true }

def rejectedUninitializedTempRead :
    TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? uninitializedTempStorage 0

def orderedAccessSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := some 40 },
        { key := 9, value := some 90 }] }

def orderedAccessRegression : TraceResult (SortSlice Nat Nat) :=
  (TraceResult.sortSliceKeysRead? orderedAccessSlice 1).bind fun entry =>
    TraceResult.sortSliceValuesWrite? orderedAccessSlice 0 entry

end TraceResult
end AccessTrace
end CPythonListsort
