/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean -/

import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Instance.CPythonListsort.Code.Assembly.AccessTrace.Part2
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

end CPythonListsort
