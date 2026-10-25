/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import Def.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/


namespace CPythonListsort

universe u

/-- Mathlib's strict-weak-order laws for the Prop-valued relation exposed by a
Boolean comparator.  This structure deliberately contains no sorting result. -/
structure BoolStrictWeakOrder {α : Type u} (lt : BoolComparator α) : Prop extends
    IsStrictWeakOrder α (fun a b => lt a b = true)

end CPythonListsort
