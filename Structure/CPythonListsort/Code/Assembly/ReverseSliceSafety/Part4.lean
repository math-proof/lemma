/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Theorem.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part3
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

/-- Public safety certificate for the complete synchronized reversal. -/
structure ReverseSliceSafetyPost
    (before : SortSlice κ ν) (valuesPresent : Bool) (base : Int) (n : Nat)
    (result : ReverseSliceResult κ ν) : Prop where
  resultEq :
    (sortsliceReverseTraced? valuesPresent before base n).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (sortsliceReverseTraced? valuesPresent before base n).trace.fuelExhausted =
      false
  accessesInBounds :
    (sortsliceReverseTraced? valuesPresent before base n).trace.allAccessesInBounds
  tempAccessesLive :
    (sortsliceReverseTraced? valuesPresent before base n).trace.tempPayloadAccessesLive
  noPushes :
    (sortsliceReverseTraced? valuesPresent before base n).trace.pushDepths = []
  exactErasure :
    (sortsliceReverseTraced? valuesPresent before base n).erase =
      sortsliceReverse? before base n
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

end ReverseSlicePhase
end CPythonListsort
