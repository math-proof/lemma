/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Assembly.AccessTrace.Part7
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

end TraceResult
end AccessTrace
end CPythonListsort
