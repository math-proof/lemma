/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import Def.CPythonListsort.Code.Correctness.ScanStepCorrectness.Part3
import Def.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness.Part2
/-!
# Equivariance under mirrored occurrence origins

Reverse-mode correctness compares the actual initially reversed execution,
whose carried origins run backwards, with a canonical execution over the
reversed source.  This file supplies the explicit relabeling and proves that
the implementation observes only occurrence values: changing every origin by
the same mirror map commutes with the data-moving evaluator.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Mirror an absolute origin inside a slice of length `size`, leaving origins
outside that slice unchanged.  The outside branch makes this a total
involution even on stale or deliberately fabricated temporary cells. -/
def mirrorOrigin (size origin : Nat) : Nat :=
  if origin < size then size - 1 - origin else origin

/-- Relabel one carried occurrence without changing its observable value. -/
def mirrorOccurrence (size : Nat) (entry : Occurrence alpha) : Occurrence alpha :=
  { value := entry.value, origin := mirrorOrigin size entry.origin }

/-- Relabel the key of one synchronized entry, preserving its payload. -/
def mirrorSortSliceEntry (size : Nat)
    (entry : SortSliceEntry (Occurrence alpha) nu) :
    SortSliceEntry (Occurrence alpha) nu :=
  { key := mirrorOccurrence size entry.key, value := entry.value }

/-- Relabel every occurrence key in a synchronized slice. -/
def mirrorSortSlice (size : Nat) (slice : SortSlice (Occurrence alpha) nu) :
    SortSlice (Occurrence alpha) nu :=
  { entries := slice.entries.map (mirrorSortSliceEntry size) }

/-- Relabel initialized temporary cells while retaining allocation metadata. -/
def mirrorTempStorage (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    TempStorage (Occurrence alpha) nu :=
  { cells := storage.cells.map (Option.map (mirrorSortSliceEntry size))
    backing := storage.backing
    hasValues := storage.hasValues }

/-- Relabel every occurrence-bearing store in a merge state.  All control,
layout, allocation, and comparator fields are retained literally. -/
def mirrorMergeState (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    MergeState (Occurrence alpha) nu :=
  { state with
    data := mirrorSortSlice size state.data
    a := mirrorTempStorage size state.a }

def mirrorCursorResult (size : Nat)
    (result : SortSlice.CursorResult (Occurrence alpha) nu) :
    SortSlice.CursorResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

def mirrorReverseSliceResult (size : Nat)
    (result : ReverseSliceResult (Occurrence alpha) nu) :
    ReverseSliceResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

/-! ## Natural-run detection -/

def mirrorCountRunResult (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    CountRunResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

end CPythonListsort
