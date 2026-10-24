/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import sympy.atlas.CPythonListsort.Code.Assembly.MergeGetmemStorageValid
import sympy.atlas.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import sympy.atlas.CPythonListsort.Code.Assembly.MergeLoSafety
import sympy.atlas.CPythonListsort.Code.Assembly.MergeHiSafety

/-!
# Semantic validation for the real merge-memory trace

`AccessTrace` deliberately stores raw, type-erased observations.  This module
states the propositions those observations must satisfy.  None of the
predicates below changes the evaluator or manufactures a reachability
relation: later assembly theorems apply them to the literal `memoryEvents`
field returned by `listSortImplTraced?`.
-/

namespace CPythonListsort

universe u v

namespace MergeMemorySnapshot

/-- The one-or-two-pointer multiplier represented by a raw snapshot. -/
def multiplier (snapshot : MergeMemorySnapshot) : Nat :=
  if snapshot.hasValues then 2 else 1

/-- Snapshot form of the signed-allocation guard limit. -/
def allocationLimit (snapshot : MergeMemorySnapshot) : Nat :=
  PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / snapshot.multiplier

/-- Literal snapshot form of `TempStorageInv`.  The released case
deliberately leaves `alloced` and `hasValues` stale. -/
def StorageInv (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots = snapshot.multiplier * snapshot.cellsSize ∧
    match snapshot.backing with
    | .inline =>
        snapshot.cellsSize = snapshot.alloced.toNat ∧
          snapshot.multiplier * snapshot.alloced.toNat ≤
            MERGESTATE_TEMP_SIZE
    | .heap => snapshot.cellsSize = snapshot.alloced.toNat
    | .released => snapshot.cellsSize = 0

/-- Snapshot backing is available for payload access. -/
def Live (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.backing ≠ .released

/-- Every main-array entry agrees with the retained values-pointer mode.
The separate Boolean equation is intentional: on an empty main array the
entrywise clause alone cannot determine the mode. -/
def ValuesMode (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.hasValues = mode ∧
    ∀ (i : Nat) (hi : i < snapshot.mainValuePresent.length),
      snapshot.mainValuePresent[i] = mode

/-- The active representation facts, excluding the selected-platform heap
upper bound.  That bound is a reachability fact threaded separately from the
inline initializer through each real allocation transition. -/
def ActiveCore (mode : Bool) (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.StorageInv ∧ snapshot.Live ∧
    snapshot.cellsSize = snapshot.alloced.toNat ∧
    snapshot.ValuesMode mode

/-- The selected-platform physical allocation ceiling. -/
def PhysicalBound (snapshot : MergeMemorySnapshot) : Prop :=
  snapshot.physicalSlots ≤ PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

/-- The intermediate released snapshot which the C control flow exposes when
`merge_getmem` leaves the signed-capacity reuse branch.  This is a raw
observation constructor: the semantic lemmas below prove that its `some`
case is exactly the state immediately after `mergeFreemem`. -/
def mergeMemoryIntermediateFree (state : MergeState κ ν) (need : PySSize) :
    Option MergeMemorySnapshot :=
  if need.sle state.alloced then none
  else some (MergeMemorySnapshot.ofState (mergeFreemem state))

/-- Raw lifecycle observation for one completed `merge_lo` call. -/
def mergeLoMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeLoResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.na
  let allocated := mergeLoAllocated call
  { direction := .lo
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Raw lifecycle observation for one completed `merge_hi` call. -/
def mergeHiMemoryCallEvent (call : MergeAtCall κ ν)
    (result : MergeHiResult κ ν) : MergeMemoryCallEvent :=
  let need : PySSize := BitVec.ofNat 64 call.nb
  let allocated := mergeHiAllocated call
  { direction := .hi
    request := need
    na := call.na
    nb := call.nb
    sourceLeftLength := call.left.len
    sourceRightLength := call.right.len
    listlen := call.state.listlen
    outcome := allocated.outcome
    before := MergeMemorySnapshot.ofState call.state
    intermediateFree := mergeMemoryIntermediateFree call.state need
    afterGetmem := MergeMemorySnapshot.ofState allocated.state
    afterMerge := MergeMemorySnapshot.ofState result.state }

/-- Snapshot-level record of the exact `merge_freemem` transition which
precedes a growing (or guard-rejected) allocation attempt. -/
def IsFreedFrom (before freed : MergeMemorySnapshot) : Prop :=
  freed.hasValues = before.hasValues ∧
    freed.alloced = before.alloced ∧
    freed.mainValuePresent = before.mainValuePresent ∧
    if before.backing = .inline then
      freed = before
    else
      freed.backing = .released ∧ freed.cellsSize = 0 ∧
        freed.physicalSlots = 0

/-- Exact successful `merge_getmem` behavior visible in a call record.
The rejected branch is deliberately absent; later proofs must derive one of
these two arms from the pending-layout request bound. -/
def GetmemValid (call : MergeMemoryCallEvent) : Prop :=
  (call.outcome = .reused ∧
      call.request.sle call.before.alloced = true ∧
      call.intermediateFree = none ∧
      call.afterGetmem = call.before) ∨
    (call.outcome = .grown ∧
      call.request.sle call.before.alloced = false ∧
      ∃ freed,
        call.intermediateFree = some freed ∧
        IsFreedFrom call.before freed ∧
        call.request.toNat ≤ call.before.allocationLimit ∧
        call.afterGetmem.backing = .heap ∧
        call.afterGetmem.hasValues = call.before.hasValues ∧
        call.afterGetmem.alloced = call.request ∧
        call.afterGetmem.cellsSize = call.request.toNat ∧
        call.afterGetmem.physicalSlots =
          call.before.multiplier * call.request.toNat ∧
        call.afterGetmem.mainValuePresent =
          call.before.mainValuePresent)

/-- The merge proper can change main-data order and temporary contents, but
not the allocation metadata installed by `merge_getmem`. -/
def MergeStorageFrame (call : MergeMemoryCallEvent) : Prop :=
  call.afterMerge.backing = call.afterGetmem.backing ∧
    call.afterMerge.hasValues = call.afterGetmem.hasValues ∧
    call.afterMerge.cellsSize = call.afterGetmem.cellsSize ∧
    call.afterMerge.alloced = call.afterGetmem.alloced ∧
    call.afterMerge.physicalSlots = call.afterGetmem.physicalSlots ∧
    call.afterMerge.mainValuePresent.length =
      call.afterGetmem.mainValuePresent.length

/-- All semantic facts required of one actual directional merge record. -/
structure Valid (mode : Bool) (call : MergeMemoryCallEvent) : Prop where
  beforeActive : call.before.ActiveCore mode
  getmemActive : call.afterGetmem.ActiveCore mode
  afterMergeActive : call.afterMerge.ActiveCore mode
  requestWord : call.request = BitVec.ofNat 64 (min call.na call.nb)
  requestNonnegative : call.request.Nonnegative
  directionalRequest :
    (call.direction = .lo ∧ call.request.toNat = call.na ∧
      call.na ≤ call.nb) ∨
    (call.direction = .hi ∧ call.request.toNat = call.nb ∧
      call.nb < call.na)
  trimmingOnlyShrinks :
    call.na + call.nb ≤
      call.sourceLeftLength.toNat + call.sourceRightLength.toNat
  sourceRunsWithinList :
    call.sourceLeftLength.toNat + call.sourceRightLength.toNat ≤
      call.listlen.toNat
  smallerHalf :
    call.request.toNat ≤ (call.na + call.nb) / 2 ∧
      (call.na + call.nb) / 2 ≤ call.listlen.toNat / 2
  keyedLimit : call.before.hasValues = true →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES / 2 = 2 ^ 59 - 1
  unkeyedLimit : call.before.hasValues = false →
    call.before.allocationLimit =
        PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES ∧
      PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES = 2 ^ 60 - 1
  requestWithinLimit : call.request.toNat ≤ call.before.allocationLimit
  getmem : call.GetmemValid
  neverGuardRejected : call.outcome ≠ .guardRejected
  requestFits : call.request.toNat ≤ call.afterGetmem.alloced.toNat
  keySlots : ∀ i, i < call.request.toNat →
    i < call.afterGetmem.physicalSlots
  valueSlots : call.before.hasValues = true →
    ∀ i, i < call.request.toNat →
      call.afterGetmem.alloced.toNat + i <
        call.afterGetmem.physicalSlots
  mergeStorageFrame : call.MergeStorageFrame
  /-- Reuse preserves an already-established bound; growth establishes it
  from the exact allocation guard. -/
  physicalBoundPreserved : call.before.PhysicalBound →
    call.afterGetmem.PhysicalBound ∧ call.afterMerge.PhysicalBound

/-- The stronger per-call projection used once the initializer's physical
bound has been threaded to this call site. -/
def Bounded (call : MergeMemoryCallEvent) : Prop :=
  call.before.PhysicalBound ∧ call.afterGetmem.PhysicalBound ∧
    call.afterMerge.PhysicalBound ∧
    ∀ freed ∈ call.intermediateFree, freed.PhysicalBound

/-- Exact snapshot-level cleanup contract, including the intentional stale
metadata exception for released heap storage. -/
def CleanupValid (mode : Bool) (before after : MergeMemorySnapshot) : Prop :=
  before.ActiveCore mode ∧ after.StorageInv ∧ after.ValuesMode mode ∧
    MergeMemoryCallEvent.IsFreedFrom before after

/-- Semantic validity of a raw event. -/
def Valid (mode : Bool) : MergeMemoryEvent → Prop
  | .initial snapshot => snapshot.ActiveCore mode
  | .mergeCall call => call.Valid mode
  | .cleanup before after => CleanupValid mode before after

/-- The state entering an event. -/
def start : MergeMemoryEvent → MergeMemorySnapshot
  | .initial snapshot => snapshot
  | .mergeCall call => call.before
  | .cleanup before _ => before

/-- The state leaving an event. -/
def finish : MergeMemoryEvent → MergeMemorySnapshot
  | .initial snapshot => snapshot
  | .mergeCall call => call.afterMerge
  | .cleanup _ after => after

end MergeMemoryEvent

namespace AccessTrace

/-- Consecutive directional call records form one real storage-state path.
The endpoints are explicit, so a list with no calls can describe only an
unchanged memory snapshot; no fabricated gap can be hidden between calls. -/
def MergeMemoryCallChain :
    MergeMemorySnapshot → List MergeMemoryCallEvent →
      MergeMemorySnapshot → Prop
  | start, [], final => start = final
  | start, call :: calls, final =>
      call.before = start ∧ MergeMemoryCallChain call.afterMerge calls final

namespace MergeMemoryCallChain

/-- Every event in the literal trace is semantically valid in the initialized
values mode. -/
def memoryEventsValid (mode : Bool) (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents, event.Valid mode

/-- A helper trace contains directional calls only; initialization and final
cleanup are owned exclusively by the top-level evaluator. -/
def onlyMergeMemoryEvents (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents, ∃ call, event = .mergeCall call

/-- All directional records in a trace carry the selected-platform physical
bound at every retained active boundary. -/
def mergeMemoryEventsBounded (trace : AccessTrace) : Prop :=
  ∀ event ∈ trace.memoryEvents,
    match event with
    | .mergeCall call => call.Bounded
    | _ => True

/-- A helper trace is exactly a continuous sequence of directional calls from
one concrete memory snapshot to another. -/
def MergeMemorySegment (start final : MergeMemorySnapshot)
    (trace : AccessTrace) : Prop :=
  ∃ calls : List MergeMemoryCallEvent,
    trace.memoryEvents = calls.map MergeMemoryEvent.mergeCall ∧
      MergeMemoryCallChain start calls final

/-- The trace segment produced from an active listsort state through its exit
contains a continuous sequence of real merge calls followed by exactly one
terminal cleanup.  Initialization is added only by `listSortImplTraced?`. -/
def MergeMemoryTail (start final : MergeMemorySnapshot)
    (trace : AccessTrace) : Prop :=
  ∃ (calls : List MergeMemoryCallEvent)
      (cleanupBefore : MergeMemorySnapshot),
    trace.memoryEvents =
      calls.map MergeMemoryEvent.mergeCall ++
        [.cleanup cleanupBefore final] ∧
      MergeMemoryCallChain start calls cleanupBefore

/-- Exact top-level shape: one initializer, zero or more directional calls,
and one terminal cleanup.  `events` is the evaluator's literal trace field;
there is no separately supplied history which could omit a call. -/
def MergeMemoryLifecycle (mode : Bool)
    (initial final : MergeMemorySnapshot) (trace : AccessTrace) : Prop :=
  ∃ (calls : List MergeMemoryCallEvent)
      (cleanupBefore : MergeMemorySnapshot),
    trace.memoryEvents =
      .initial initial ::
        (calls.map MergeMemoryEvent.mergeCall ++
          [.cleanup cleanupBefore final]) ∧
    MergeMemoryCallChain initial calls cleanupBefore ∧
    initial.ActiveCore mode ∧
    (∀ call ∈ calls, call.Valid mode) ∧
    (∀ call ∈ calls, call.Bounded) ∧
    MergeMemoryEvent.CleanupValid mode cleanupBefore final
