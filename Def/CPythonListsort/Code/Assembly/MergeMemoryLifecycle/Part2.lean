/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeMemoryLifecycle.lean -/

import Structure.CPythonListsort.Code.Assembly.MergeGetmemRequestBound
import Def.CPythonListsort.Code.Assembly.MergeGetmemStorageValid.Part2
import Def.CPythonListsort.Code.Assembly.MergeMemcpyProvenance
import Structure.CPythonListsort.Code.Assembly.MergeLoSafety.Part4
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Structure.CPythonListsort.Code.Assembly.MergeMemoryLifecycle
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

end MergeMemoryCallChain
end AccessTrace
end CPythonListsort
