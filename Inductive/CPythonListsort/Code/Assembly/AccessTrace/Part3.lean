/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Assembly.AccessTrace.Part3
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

end CPythonListsort
