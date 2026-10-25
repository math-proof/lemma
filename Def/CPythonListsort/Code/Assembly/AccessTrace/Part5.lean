/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Assembly.AccessTrace.Part6
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

end AccessTrace
end CPythonListsort
