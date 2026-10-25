/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Theorem.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part4
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

/-! ## Branch and failure anti-vacuity regressions -/

def reverseRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 12 },
        { key := 3, value := some 13 }] }

def reverseNoValuesRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := none },
        { key := 1, value := none },
        { key := 2, value := none },
        { key := 3, value := none }] }

end ReverseSlicePhase
end CPythonListsort
