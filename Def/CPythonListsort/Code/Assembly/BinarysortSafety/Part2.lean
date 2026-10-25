/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Theorem.CPythonListsort.Code.Assembly.BinarysortSafety.Part5
/-!
# `binarysort` safety

This module instruments CPython's stable binary insertion sort directly from
the traced `SortSlice` primitives.  The trace follows the source phases: read
the key pivot, probe binary-search midpoints, shift keys from right to left,
write the key pivot, and then (when values storage is present) read, shift, and
write the synchronized payloads.  Explicit fuel exhaustion remains observable
but is proved unreachable on source-admitted calls.

Version-one delta: the pinned C `IFLT` can jump to `fail` when comparison
raises, while this snapshot model's `BoolComparator` is pure and total.  The
traced evaluator therefore has no comparator-failure result or comparator
event; exact erasure below is to the reviewed Lean transcription on that
explicitly narrower comparator model.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace BinarysortTraceSafe

def binarysortRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 1, value := some 10 }] }

def binarysortEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 2, value := some 21 }] }

def binarysortSingletonRegressionSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 1, value := some 10 }] }

def binarysortPairRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := some 20 },
        { key := 1, value := some 10 }] }

def binarysortUnkeyedRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 2, value := none },
        { key := 1, value := none }] }

def binarysortTaggedEqualRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 20 },
        { key := 1, value := some 12 }] }

def binarysortRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data := binarysortEqualRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def binarysortSingletonRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 1
    data := binarysortSingletonRegressionSlice }

def binarysortPairRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortPairRegressionSlice }

def binarysortUnkeyedRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 2
    data := binarysortUnkeyedRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false } }

def binarysortTaggedEqualRegressionState : MergeState Nat Nat :=
  { binarysortRegressionState with
    listlen := 4
    data := binarysortTaggedEqualRegressionSlice }

end BinarysortTraceSafe
end CPythonListsort
