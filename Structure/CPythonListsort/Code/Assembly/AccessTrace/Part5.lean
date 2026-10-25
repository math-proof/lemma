/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Def.CPythonListsort.Code.Assembly.AccessTrace.Part4
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

end CPythonListsort
