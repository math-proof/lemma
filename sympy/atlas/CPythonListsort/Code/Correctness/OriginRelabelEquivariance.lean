/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.ScanStepCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.MergeForceCollapseCorrectness

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

@[simp] theorem mirrorCountRunResult_slice (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorCountRunResult_length (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).length = result.length := rfl

@[simp] theorem mirrorCountRunResult_fuel (size : Nat)
    (result : CountRunResult (Occurrence alpha) nu) :
    (mirrorCountRunResult size result).fuelExhausted = result.fuelExhausted := rfl

def mirrorReverseEqualResult (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    ReverseEqualResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorReverseEqualResult_slice (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorReverseEqualResult_fuel (size : Nat)
    (result : ReverseEqualResult (Occurrence alpha) nu) :
    (mirrorReverseEqualResult size result).fuelExhausted = result.fuelExhausted := rfl

def mirrorDescendingScanResult (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    DescendingScanResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorDescendingScanResult_slice (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).slice =
      mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorDescendingScanResult_length (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).length = result.length := rfl

@[simp] theorem mirrorDescendingScanResult_equalTail (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).equalTail = result.equalTail := rfl

@[simp] theorem mirrorDescendingScanResult_fuel (size : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) :
    (mirrorDescendingScanResult size result).fuelExhausted =
      result.fuelExhausted := rfl

/-! ## Stable binary insertion -/

def mirrorBinarysortResult (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    BinarysortResult (Occurrence alpha) nu :=
  { result with slice := mirrorSortSlice size result.slice }

@[simp] theorem mirrorBinarysortResult_slice (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    (mirrorBinarysortResult size result).slice = mirrorSortSlice size result.slice := rfl

@[simp] theorem mirrorBinarysortResult_fuel (size : Nat)
    (result : BinarysortResult (Occurrence alpha) nu) :
    (mirrorBinarysortResult size result).fuelExhausted = result.fuelExhausted := rfl

/-- Reverse-oriented pending correctness: the structural and sortedness facts
hold on the mirrored state itself, while stability is checked after applying
the origin involution back to the canonical orientation. -/
structure CanonicalMirroredPendingRunsCorrect (lt : BoolComparator alpha)
    (input : Array alpha) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  layout : PendingLayout state scanned
  runSorted : ∀ run ∈ state.pending.toList,
    Sorted (occurrenceComparator lt) (pendingRunOccurrenceKeys state run)
  stableAfterUnmirror : StableOccurrencePermutation lt
    (canonicalOccurrenceSegment input state.basekeys scanned)
    ((pendingOccurrenceKeys state).map (mirrorOccurrence size))

/-- Whole-entry snapshot relation for a mirrored execution.  Unmirroring each
current entry must recover a permutation of the absolutely tagged source. -/
def CanonicalMirroredEntrySnapshotPermutation (source : SortSlice alpha nu)
    (size : Nat) (current : SortSlice (Occurrence alpha) nu) : Prop :=
  (current.entries.map (mirrorSortSliceEntry size)).toList.Perm
    (tagSortSliceOccurrences source).entries.toList

/-- Unscanned-suffix relation for a mirrored execution.  Bounds are stated on
the real mirrored state; its suffix agrees with the canonical source after
applying the origin involution back to every entry. -/
structure CanonicalMirroredScanRemainderEntriesMatch
    (source : SortSlice alpha nu) (size : Nat)
    (state : MergeState (Occurrence alpha) nu) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    ((sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).map
        (mirrorSortSliceEntry size)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

/-! ## Kernel-checkable nonidentity regression -/

private def originRelabelRegressionOccurrence : Occurrence Nat :=
  { value := 17, origin := 0 }
