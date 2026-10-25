/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety
/-!
# Slice-reversal safety

This module instruments the two physical phases of CPython's
`sortslice_reverse`.  A key phase is always executed; a synchronized-values
phase is executed from the same pre-state exactly when the explicit values
mode is enabled.  Each phase performs the reviewed reversal itself through
typed access wrappers, so the trace is produced by execution rather than
attached to an independently computed result.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseSlicePhase

structure ReverseTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

end ReverseSlicePhase
end CPythonListsort
