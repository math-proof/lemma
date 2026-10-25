/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Mathlib.Data.List.InsertIdx
import Structure.CPythonListsort.Code.Correctness.BinarysortCorrectness.Part2
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

def binarysortCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def binarysortCorrectnessEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 1, origin := 1 }, value := some 11 },
        { key := { value := 2, origin := 2 }, value := some 20 },
        { key := { value := 1, origin := 3 }, value := some 12 }] }

def binarysortCorrectnessEqualState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 4
    basekeys := 0
    data := binarysortCorrectnessEqualSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator binarysortCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def binarysortCorrectnessOffsetSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 99, origin := 90 }, value := some 900 },
        { key := { value := 2, origin := 0 }, value := some 20 },
        { key := { value := 1, origin := 1 }, value := some 10 },
        { key := { value := 2, origin := 2 }, value := some 21 },
        { key := { value := 88, origin := 91 }, value := some 800 }] }

def binarysortCorrectnessOffsetState :
    MergeState (Occurrence Nat) Nat :=
  { binarysortCorrectnessEqualState with
    listlen := 5
    data := binarysortCorrectnessOffsetSlice }

end CPythonListsort
