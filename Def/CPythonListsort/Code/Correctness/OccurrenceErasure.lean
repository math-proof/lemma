/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelScan.Part2
/-!
# Erasure of occurrence tags

The functional-correctness development runs the implementation on keys tagged
with their original positions.  This module proves that those tags are ghost
data for execution: after structurally erasing every occurrence key, the full
tagged evaluator is exactly the ordinary untagged evaluator.  Optional payloads
and all control, allocation, pending-run, and fuel fields are preserved.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Forget the origin component of one occurrence-bearing synchronized entry. -/
def eraseOccurrenceEntry
    (entry : SortSliceEntry (Occurrence alpha) nu) : SortSliceEntry alpha nu :=
  { key := entry.key.value
    value := entry.value }

/-- Forget occurrence origins throughout a synchronized slice. -/
def eraseOccurrenceSlice
    (slice : SortSlice (Occurrence alpha) nu) : SortSlice alpha nu :=
  { entries := slice.entries.map eraseOccurrenceEntry }

/-- Project an occurrence comparator to values by supplying irrelevant origins. -/
def eraseOccurrenceComparator
    (compare : BoolComparator (Occurrence alpha)) : BoolComparator alpha :=
  fun left right =>
    compare { value := left, origin := 0 } { value := right, origin := 0 }

/-- Forget occurrence origins in initialized temporary cells. -/
def eraseOccurrenceTempStorage
    (storage : TempStorage (Occurrence alpha) nu) : TempStorage alpha nu :=
  { cells := storage.cells.map (Option.map eraseOccurrenceEntry)
    backing := storage.backing
    hasValues := storage.hasValues }

/-- Structurally erase occurrence origins from a merge state. -/
def eraseOccurrenceMergeState
    (state : MergeState (Occurrence alpha) nu) : MergeState alpha nu :=
  { min_gallop := state.min_gallop
    listlen := state.listlen
    basekeys := state.basekeys
    data := eraseOccurrenceSlice state.data
    a := eraseOccurrenceTempStorage state.a
    alloced := state.alloced
    pending := state.pending
    key_compare := eraseOccurrenceComparator state.key_compare
    mr_current := state.mr_current
    mr_e := state.mr_e
    mr_mask := state.mr_mask }

/-- Structurally erase occurrence origins from a top-level result. -/
def eraseOccurrenceListSortImplResult
    (result : ListSortImplResult (Occurrence alpha) nu) :
    ListSortImplResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

def eraseOccurrenceCursorResult
    (result : SortSlice.CursorResult (Occurrence alpha) nu) :
    SortSlice.CursorResult alpha nu :=
  { slice := eraseOccurrenceSlice result.slice
    dst := result.dst
    src := result.src }

def eraseOccurrenceReverseSliceResult
    (result : ReverseSliceResult (Occurrence alpha) nu) :
    ReverseSliceResult alpha nu :=
  { slice := eraseOccurrenceSlice result.slice
    fuelExhausted := result.fuelExhausted }

/-! ## Allocation and galloping -/

def eraseOccurrenceMergeGetmemResult
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    MergeGetmemResult alpha nu :=
  { result with state := eraseOccurrenceMergeState result.state }

/-! ## Natural-run detection -/

def eraseOccurrenceCountRunResult
    (result : CountRunResult (Occurrence alpha) nu) :
    CountRunResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

def eraseOccurrenceReverseEqualResult
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    ReverseEqualResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

def eraseOccurrenceDescendingScanResult
    (result : DescendingScanResult (Occurrence alpha) nu) :
    DescendingScanResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

/-! ## Stable binary insertion -/

def eraseOccurrenceBinarysortResult
    (result : BinarysortResult (Occurrence alpha) nu) :
    BinarysortResult alpha nu :=
  { result with slice := eraseOccurrenceSlice result.slice }

end CPythonListsort
