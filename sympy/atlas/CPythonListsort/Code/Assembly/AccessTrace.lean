/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.MergeMemory

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

/-- Whether an ordinary indexed access attempts to read or write its region. -/
inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- The array-like region addressed by an ordinary access attempt.

The backing constructor argument is observed at the temporary payload access
itself.  Encoding it in the region prevents a temporary event from silently
omitting the backing state.  Pending-stack `Array.push` is not a
`pendingRuns` access; only indexed reads and writes use that constructor. -/
inductive AccessRegion where
  | inputKeys
  | synchronizedValues
  | tempPayload (backingAtAttempt : TempBacking)
  | pendingRuns
  deriving DecidableEq, Repr

/-- One ordinary indexed access attempt.  Signed indices are retained so a
negative rejected attempt is represented faithfully rather than coerced to a
natural number.  `extent` is the region's length at the time of the attempt. -/
structure AccessEvent where
  kind : AccessKind
  region : AccessRegion
  index : Int
  extent : Nat
  deriving DecidableEq, Repr

namespace AccessEvent

/-- The attempted signed index lies in the half-open interval `[0, extent)`. -/
def InBounds (event : AccessEvent) : Prop :=
  0 ≤ event.index ∧ event.index < Int.ofNat event.extent

instance (event : AccessEvent) : Decidable event.InBounds :=
  inferInstanceAs (Decidable (0 ≤ event.index ∧ event.index < Int.ofNat event.extent))

/-- A temporary payload attempt observes live rather than released backing.
Non-temporary events satisfy this predicate vacuously. -/
def TempPayloadLive (event : AccessEvent) : Prop :=
  match event.region with
  | .tempPayload backing => backing ≠ .released
  | _ => True

instance (event : AccessEvent) : Decidable event.TempPayloadLive := by
  unfold TempPayloadLive
  split <;> infer_instance

end AccessEvent

/-! ## Type-erased merge-memory history -/

/-- The storage facts retained at one merge-memory boundary.

The snapshot deliberately contains only decidable, type-erased observations.
`mainValuePresent` records, in main-array order, whether each entry carries a
synchronized value.  It records the raw state rather than a Boolean claiming
that any storage invariant holds; later safety modules must validate the
snapshot independently. -/
structure MergeMemorySnapshot where
  backing : TempBacking
  hasValues : Bool
  cellsSize : Nat
  alloced : PySSize
  physicalSlots : Nat
  mainValuePresent : List Bool
  deriving DecidableEq, Repr

namespace MergeMemorySnapshot

/-- Type-erase exactly the merge-memory observations present in `state`. -/
def ofState (state : MergeState κ ν) : MergeMemorySnapshot :=
  { backing := state.a.backing
    hasValues := state.a.hasValues
    cellsSize := state.a.cells.size
    alloced := state.alloced
    physicalSlots := state.a.physicalSlots
    mainValuePresent :=
      state.data.entries.toList.map fun entry => entry.value.isSome }

end MergeMemorySnapshot

/-- Which directional merge consumed one `merge_getmem` result. -/
inductive MergeMemoryDirection where
  | lo
  | hi
  deriving DecidableEq, Repr

/-- Raw observations spanning one directional merge call.

`sourceLeftLength` and `sourceRightLength` retain the two run lengths before
`merge_at` trimming; `na` and `nb` are the lengths actually passed to the
directional merge.  `intermediateFree` is an observation slot, not a claim:
the later safety layer must prove when it is `none`, when it is `some`, and
that any supplied snapshot is the state immediately after `merge_freemem`.
Likewise, this record does not assert that `request`, `outcome`, or any of the
snapshots agree with the modeled transition. -/
structure MergeMemoryCallEvent where
  direction : MergeMemoryDirection
  request : PySSize
  na : Nat
  nb : Nat
  sourceLeftLength : PySSize
  sourceRightLength : PySSize
  listlen : PySSize
  outcome : MergeGetmemOutcome
  before : MergeMemorySnapshot
  intermediateFree : Option MergeMemorySnapshot
  afterGetmem : MergeMemorySnapshot
  afterMerge : MergeMemorySnapshot
  deriving DecidableEq, Repr

/-- Chronological merge-memory boundary observations.

These constructors are intentionally non-validating.  They retain enough raw
data for a separate lifecycle predicate to compare the snapshots with
`merge_init`, `merge_getmem`, the directional merge, and `merge_freemem`
without making any of those obligations true by construction. -/
inductive MergeMemoryEvent where
  | initial (state : MergeMemorySnapshot)
  | mergeCall (call : MergeMemoryCallEvent)
  | cleanup (before after : MergeMemorySnapshot)
  deriving DecidableEq, Repr

/-! ## Type-erased policy history -/

/-- The source interval occupied by one pending run.

This is a raw, type-erased observation.  In particular, the structure itself
does not assert positivity, adjacency, or containment in the input. -/
structure RunSpan where
  base : Nat
  len : Nat
  deriving DecidableEq, Repr

namespace RunSpan

/-- Forget the pending run's power and retain its source interval. -/
def ofPendingRun (run : PendingRun) : RunSpan :=
  { base := run.base, len := run.len.toNat }

end RunSpan

/-- Raw observations attached to the successful push of one formed run.

`naturalLength` is the length returned by run discovery, `target` is the
current adaptive-minrun target, and `remainingBefore` is the unscanned length
before this run is consumed.  Keeping all three separate makes both the
extended-short-run and already-long-natural-run cases observable. -/
structure PendingPushEvent where
  run : RunSpan
  depthAfter : Nat
  naturalLength : Nat
  target : Nat
  remainingBefore : Nat
  deriving DecidableEq, Repr

/-- One logical merge, recorded at the successful pending-stack splice.

The two operands are the full pre-trimming pending runs.  Consequently, this
event remains present when galloping later discovers that no directional data
movement is needed. -/
structure LogicalMergeEvent where
  index : Nat
  left : RunSpan
  right : RunSpan
  deriving DecidableEq, Repr

/-- Policy-level events needed to reconstruct formed leaves and logical merge
nodes independently of physical access and merge-memory traces. -/
inductive PolicyEvent where
  | formed (push : PendingPushEvent)
  | merge (event : LogicalMergeEvent)
  deriving DecidableEq, Repr

/-- Ordered observations made by an instrumented evaluator.

`accesses`, `pushDepths`, `memoryEvents`, and `policyEvents` are chronological
within their respective channels.  A `pushDepths` entry is the pending-array
size *after* one unconditional push.  Fuel exhaustion composes by Boolean
disjunction. -/
structure AccessTrace where
  accesses : List AccessEvent
  pushDepths : List Nat
  memoryEvents : List MergeMemoryEvent := []
  policyEvents : List PolicyEvent := []
  fuelExhausted : Bool
  deriving DecidableEq, Repr

namespace AccessTrace

/-- The trace containing no observations. -/
def empty : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- Sequential trace composition, with the left trace occurring first. -/
def compose (earlier later : AccessTrace) : AccessTrace :=
  { accesses := earlier.accesses ++ later.accesses
    pushDepths := earlier.pushDepths ++ later.pushDepths
    memoryEvents := earlier.memoryEvents ++ later.memoryEvents
    policyEvents := earlier.policyEvents ++ later.policyEvents
    fuelExhausted := earlier.fuelExhausted || later.fuelExhausted }

/-- Low-level constructor for one access-attempt trace.  It intentionally
accepts an explicit region and extent so the typed wrappers later in this file
can share one implementation.  Instrumented listsort code should use those
state-derived wrappers instead of manufacturing labels or extents itself.  No
bounds or liveness filter is applied: rejected attempts remain observable. -/
def singletonAccess (kind : AccessKind) (region : AccessRegion)
    (index : Int) (extent : Nat) : AccessTrace :=
  { accesses := [{ kind := kind, region := region, index := index, extent := extent }]
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- The local trace emitted after one pending-stack push. -/
def singletonPushDepth (depth : Nat) : AccessTrace :=
  { accesses := []
    pushDepths := [depth]
    memoryEvents := []
    policyEvents := []
    fuelExhausted := false }

/-- The local trace containing one raw merge-memory boundary observation. -/
def singletonMemoryEvent (event : MergeMemoryEvent) : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := [event]
    policyEvents := []
    fuelExhausted := false }

/-- The local trace containing one raw policy observation. -/
def singletonPolicyEvent (event : PolicyEvent) : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := [event]
    fuelExhausted := false }

/-- The aligned depth and policy observations emitted by a formed-run push. -/
def singletonFormedRun (event : PendingPushEvent) : AccessTrace :=
  { accesses := []
    pushDepths := [event.depthAfter]
    memoryEvents := []
    policyEvents := [.formed event]
    fuelExhausted := false }

/-- A local evaluator exhausted one of its explicit fuel counters. -/
def exhausted : AccessTrace :=
  { accesses := []
    pushDepths := []
    memoryEvents := []
    policyEvents := []
    fuelExhausted := true }

/-- Every ordinary access attempt is within the extent recorded beside it. -/
def allAccessesInBounds (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.accesses, event.InBounds

instance (trace : AccessTrace) : Decidable trace.allAccessesInBounds :=
  inferInstanceAs (Decidable (∀ event ∈ trace.accesses, event.InBounds))

/-- No temporary payload access attempt observed released backing.

Because this quantifies over all recorded attempts, an out-of-bounds temporary
attempt is not filtered out before the storage-liveness check. -/
def tempPayloadAccessesLive (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.accesses, event.TempPayloadLive

instance (trace : AccessTrace) : Decidable trace.tempPayloadAccessesLive :=
  inferInstanceAs (Decidable (∀ event ∈ trace.accesses, event.TempPayloadLive))

/-- Maximum recorded post-push depth, with zero for a trace with no pushes. -/
def stackDepthMax (trace : AccessTrace) : Nat :=
  trace.pushDepths.foldl Nat.max 0

@[simp]
theorem allAccessesInBounds_compose (earlier later : AccessTrace) :
    (compose earlier later).allAccessesInBounds ↔
      earlier.allAccessesInBounds ∧ later.allAccessesInBounds := by
  simp only [allAccessesInBounds, compose, List.mem_append]
  aesop

@[simp]
theorem tempPayloadAccessesLive_empty : empty.tempPayloadAccessesLive := by
  simp [tempPayloadAccessesLive, empty]

@[simp]
theorem tempPayloadAccessesLive_compose (earlier later : AccessTrace) :
    (compose earlier later).tempPayloadAccessesLive ↔
      earlier.tempPayloadAccessesLive ∧ later.tempPayloadAccessesLive := by
  simp only [tempPayloadAccessesLive, compose, List.mem_append]
  aesop

/-- The result type used by local instrumented evaluators.

An invalid modeled operation returns `none`, but its already-produced trace is
retained.  Successful continuations compose their observations in order. -/
structure TraceResult (α : Type u) where
  result : Option α
  trace : AccessTrace
  deriving DecidableEq, Repr

namespace TraceResult

/-- Forget instrumentation and recover the underlying partial result. -/
def erase (current : TraceResult α) : Option α :=
  current.result

/-- A successful operation with no local observations. -/
def pure (value : α) : TraceResult α :=
  { result := some value, trace := AccessTrace.empty }

/-- A failed operation with no local observations.  Accessing evaluators should
instead use `captureAccess` so the rejected attempt is not erased. -/
def failure : TraceResult α :=
  { result := none, trace := AccessTrace.empty }

/-- Short-circuiting sequential composition for local instrumented evaluators. -/
def bind (current : TraceResult α) (next : α → TraceResult β) : TraceResult β :=
  match current.result with
  | none => { result := none, trace := current.trace }
  | some value =>
      let following := next value
      { result := following.result
        trace := current.trace.compose following.trace }

/-- Transform a successful local result without changing its observations. -/
def map (current : TraceResult α) (transform : α → β) : TraceResult β :=
  { result := current.result.map transform
    trace := current.trace }

/-- Record one merge-memory boundary before all observations already present
in `current`.  This operation never changes success or failure. -/
def prependMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) : TraceResult α :=
  { result := current.result
    trace := (AccessTrace.singletonMemoryEvent event).compose current.trace }

/-- Record one merge-memory boundary after all observations already present
in `current`.  This operation never changes success or failure. -/
def appendMemoryEvent (current : TraceResult α)
    (event : MergeMemoryEvent) : TraceResult α :=
  { result := current.result
    trace := current.trace.compose (AccessTrace.singletonMemoryEvent event) }

/-- Append a boundary observation exactly when the modeled operation
succeeds.  A failed operation retains its existing trace and does not invent
a completed transition.  The event is computed from the actual successful
result, rather than from a separately supplied witness. -/
def recordSuccessMemoryEvent (current : TraceResult α)
    (event : α → MergeMemoryEvent) : TraceResult α :=
  match current.result with
  | none => current
  | some value => current.appendMemoryEvent (event value)

/-- Record one policy event after all observations already present in
`current`.  This operation never changes success or failure. -/
def appendPolicyEvent (current : TraceResult α)
    (event : PolicyEvent) : TraceResult α :=
  { result := current.result
    trace := current.trace.compose (AccessTrace.singletonPolicyEvent event) }

/-- Append a policy event exactly when the modeled operation succeeds.

A failed operation retains its attempted lower-level accesses but does not
invent a completed logical transition.  Computing the event from the returned
value also permits future callers to retain result-dependent observations. -/
def recordSuccessPolicyEvent (current : TraceResult α)
    (event : α → PolicyEvent) : TraceResult α :=
  match current.result with
  | none => current
  | some value => current.appendPolicyEvent (event value)

/-- The trace side of `bind`: a rejected first operation retains its local
trace, while a successful continuation appends its trace in execution order. -/
theorem trace_bind (current : TraceResult α) (next : α → TraceResult β) :
    (current.bind next).trace =
      match current.result with
      | none => current.trace
      | some value => current.trace.compose (next value).trace := by
  cases current with
  | mk result trace =>
      cases result <;> rfl

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

private def accessTraceRegressionRun : PendingRun :=
  { base := 0, len := 1, power := none }

/-- A concrete pending array at the C capacity, used only to demonstrate the
trace semantics without requiring an otherwise irrelevant `MergeState`. -/
private def accessTraceCapacityPending : Array PendingRun :=
  Array.replicate MAX_MERGE_PENDING accessTraceRegressionRun

/-- The same total push performed by `pushPendingRunTraced`, projected to the
pending array for a closed executable capacity regression. -/
private def accessTraceForcedPush : TraceResult (Array PendingRun) :=
  let pushed := accessTraceCapacityPending.push accessTraceRegressionRun
  { result := some pushed
    trace := AccessTrace.singletonPushDepth pushed.size }

private def releasedTempStorage : TempStorage Nat Nat :=
  { cells := #[]
    backing := .released
    hasValues := true }

private def rejectedReleasedTempRead : TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? releasedTempStorage 0

private def uninitializedTempStorage : TempStorage Nat Nat :=
  { cells := #[none]
    backing := .inline
    hasValues := true }

private def rejectedUninitializedTempRead :
    TraceResult (SortSliceEntry Nat Nat) :=
  TraceResult.tempPayloadRead? uninitializedTempStorage 0

private def orderedAccessSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := some 40 },
        { key := 9, value := some 90 }] }

private def orderedAccessRegression : TraceResult (SortSlice Nat Nat) :=
  (TraceResult.sortSliceKeysRead? orderedAccessSlice 1).bind fun entry =>
    TraceResult.sortSliceValuesWrite? orderedAccessSlice 0 entry
