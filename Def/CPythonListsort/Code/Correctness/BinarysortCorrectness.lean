/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Mathlib.Data.List.InsertIdx
/-!
# Functional correctness of `binarysort`

This file proves correctness of the reviewed binary-insertion transcription on
occurrence-carrying keys.  The proof is about the same traced execution covered
by `binarysort_safe`: raw functional correctness is identified with that result
through exact erasure, rather than through a second sorting implementation.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

variable {beta kappa rho : Type*}

/-- Mathematical effect of saving the entry at `stop`, shifting
`[insert, stop)` one cell right, and writing the saved entry at `insert`. -/
def insertEarlierEntries (xs : Array beta) (insert stop : Nat)
    (pivot : beta) : Array beta :=
  ((xs.extract 0 insert ++ #[pivot]) ++ xs.extract insert stop) ++
    xs.extract (stop + 1) xs.size

end CPythonListsort
