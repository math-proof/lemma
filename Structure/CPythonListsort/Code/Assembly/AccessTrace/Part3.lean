/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Inductive.CPythonListsort.Code.Assembly.AccessTrace.Part2
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

end CPythonListsort
