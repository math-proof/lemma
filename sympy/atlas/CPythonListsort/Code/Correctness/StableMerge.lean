/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/StableMerge.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.Order
import sympy.atlas.CPythonListsort.Code.Correctness.DescendingRunInvariant
import sympy.atlas.CPythonListsort.Code.Transcription.SortSlice
import Mathlib.Data.List.Sort

/-!
# Pure stable-merge specification

`merge_lo` and `merge_hi` implement the same mathematical merge while moving
in opposite physical directions.  This file fixes that shared target before
either machine proof reasons about cursors or temporary storage.

The Boolean merge relation selects the left occurrence unless the right value
is strictly smaller.  Comparator-equivalent values therefore select the left
occurrence, exactly matching CPython's stability rule.  Payload-carrying entries
are merged by their occurrence-tagged keys, so every payload remains paired
with its original key occurrence.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Stable non-strict merge comparison on occurrence-tagged keys: choose the
left key precisely when the right key is not strictly before it. -/
def stableOccurrenceLE (lt : BoolComparator alpha)
    (left right : Occurrence alpha) : Bool :=
  !(lt right.value left.value)

/-- Whole-entry lift of `stableOccurrenceLE`.  The decision inspects only keys,
while `List.merge` moves the complete key/payload entry. -/
def stableEntryLE (lt : BoolComparator alpha)
    (left right : SortSliceEntry (Occurrence alpha) nu) : Bool :=
  stableOccurrenceLE lt left.key right.key

/-- The mathematical stable merge of two occurrence sequences. -/
def stableOccurrenceMerge (lt : BoolComparator alpha)
    (left right : List (Occurrence alpha)) : List (Occurrence alpha) :=
  List.merge left right (stableOccurrenceLE lt)

/-- The mathematical stable merge of two whole-entry sequences. -/
def stableEntryMerge (lt : BoolComparator alpha)
    (left right : List (SortSliceEntry (Occurrence alpha) nu)) :
    List (SortSliceEntry (Occurrence alpha) nu) :=
  List.merge left right (stableEntryLE lt)

/-! ## Tie-direction and payload regressions -/

private def decadeLt (left right : Nat) : Bool :=
  decide (left / 10 < right / 10)

private def stableMergeLeftEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 3 }, value := some 110 }

private def stableMergeRightEquivalentEntry :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 19, origin := 8 }, value := some 190 }

private def stableMergeLargerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 21, origin := 1 }, value := some 210 }

private def stableMergeSmallerEntry : SortSliceEntry (Occurrence Nat) Nat :=
  { key := { value := 11, origin := 7 }, value := some 110 }
