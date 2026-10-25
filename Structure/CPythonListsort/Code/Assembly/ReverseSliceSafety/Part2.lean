/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Theorem.CPythonListsort.Code.Assembly.ReverseSliceSafety
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

structure ReversePhaseLoopSafetyPost
    (fuel : Nat) (phase : ReverseSlicePhase) (before : SortSlice κ ν)
    (lo hi : Int) (valuesPresent : Bool)
    (result : ReverseSliceResult κ ν) : Prop where
  resultEq :
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe : ReverseTraceSafe
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi)
  exactErasure :
    (reverseSlicePhaseLoopTraced? fuel phase before lo hi).erase =
      reverseSliceLoop? fuel before lo hi
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

end ReverseSlicePhase
end CPythonListsort
