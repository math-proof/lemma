/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
import Def.CPythonListsort.Code.Assembly.Order.Part3
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- A modeled output whose occurrence tags have travelled with its values. -/
structure TaggedOutput (α : Type u) where
  occurrences : Array (Occurrence α)
  deriving DecidableEq, Repr

end CPythonListsort
