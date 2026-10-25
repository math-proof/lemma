/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Mathlib.Data.List.InsertIdx
import Structure.CPythonListsort.Code.Correctness.BinarysortCorrectness
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

/-! ## One stable insertion step -/

/-- Move the entry selected at `k` to insertion point `p`. -/
def moveEarlier (xs : List beta) (p k : Nat) (pivot : beta) : List beta :=
  xs.take p ++ pivot :: ((xs.drop p).take (k - p) ++ xs.drop (k + 1))

end CPythonListsort
