/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.PendingRunCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.SortSliceRange
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortInputMode
import sympy.atlas.CPythonListsort.Code.Transcription.ListSortImpl
import Mathlib

/-!
# Unscanned-snapshot correctness

`PendingRunsCorrect` intentionally describes only the prefix already represented
by the pending stack.  The scan induction also needs a separate fact saying
that the still-unscanned keys are the untouched, absolutely tagged suffix of
the original snapshot.  Keeping that fact here avoids strengthening the
already-reviewed pending-run invariant.
-/

namespace CPythonListsort

universe u v

/-! ## Whole-entry occurrence tagging -/

/-- Attach an absolute occurrence index to every key in a complete
`SortSlice`, without changing the payload paired with that key.  Tagging the
whole slice before selecting a range prevents a nonzero-base subrange from
being accidentally retagged relative to zero. -/
def tagSortSliceOccurrences (slice : SortSlice κ ν) :
    SortSlice (Occurrence κ) ν :=
  { entries := slice.entries.zipIdx.map fun entry =>
      { key := { value := entry.1.key, origin := entry.2 }
        value := entry.1.value } }

/-- Occurrence tagging preserves the input's key/payload representation mode. -/
theorem tagSortSliceOccurrences_valuesMode
    {hasKeyfunc : Bool} {slice : SortSlice κ ν}
    (h : SortSlice.ValuesModeInvariant hasKeyfunc slice) :
    SortSlice.ValuesModeInvariant hasKeyfunc (tagSortSliceOccurrences slice) := by
  intro index hindex
  have hsource : index < slice.entries.size := by simpa using hindex
  have hmode := h index hsource
  unfold SortSlice.EntryMatchesValuesMode at hmode ⊢
  split <;> simpa [tagSortSliceOccurrences] using hmode

namespace ListSortInput

/-- Lift a validated keyed or unkeyed input to absolute occurrence keys while
retaining every payload and the same `hasKeyfunc` mode. -/
def withOccurrenceKeys (input : ListSortInput κ ν) :
    ListSortInput (Occurrence κ) ν where
  slice := tagSortSliceOccurrences input.slice
  hasKeyfunc := input.hasKeyfunc
  valuesMode := tagSortSliceOccurrences_valuesMode input.valuesMode

end ListSortInput

/-- Whole-entry companion to `ScanRemainderMatches`.  It says that the
unscanned suffix still contains exactly the tagged source entries, including
each optional payload, and exposes every clipping bound explicitly. -/
structure ScanRemainderEntriesMatch (source : SortSlice κ ν)
    (state : MergeState (Occurrence κ) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  source_stop_le :
    state.basekeys + state.listlen.toNat ≤ source.entries.size
  entries_eq :
    (sortSliceRangeEntries state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      (sortSliceRangeEntries (tagSortSliceOccurrences source)
        (state.basekeys + scanned)
        (state.listlen.toNat - scanned)).toList

/-- The unscanned state suffix is exactly the corresponding absolute-origin
segment of the original input.

The three bounds are part of the proposition rather than implicit clipping
assumptions.  The invariant has no comparator parameter: it is a snapshot and
frame property, independent of ordering laws. -/
structure ScanRemainderMatches (input : Array α)
    (state : MergeState (Occurrence α) ν) (scanned : Nat) : Prop where
  scanned_le : scanned ≤ state.listlen.toNat
  state_stop_le :
    state.basekeys + state.listlen.toNat ≤ state.data.entries.size
  input_stop_le : state.basekeys + state.listlen.toNat ≤ input.size
  keys_eq :
    (sortSliceRangeKeys state.data (state.basekeys + scanned)
      (state.listlen.toNat - scanned)).toList =
      canonicalOccurrenceSegment input (state.basekeys + scanned)
        (state.listlen.toNat - scanned)

namespace ScanRemainderMatches

/-! ## Initialization and anti-vacuity regressions -/

/-- Canonically tagged unkeyed input used by the occurrence-carrying
correctness execution. -/
def occurrenceInputSlice (input : Array α) : SortSlice (Occurrence α) PUnit :=
  { entries := (tagOccurrences input).map fun key =>
      { key := key, value := none } }

private def scanRemainderRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def scanRemainderRegressionEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

private def scanRemainderRegressionInput : Array Nat :=
  #[1, 2]

/-- Empty pending coverage at `scanned = 0`, but with a deliberately corrupted
first unscanned key. -/
private def scanRemainderWrongSuffixState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 0
    data :=
      { entries :=
          #[scanRemainderRegressionEntry 99 0,
            scanRemainderRegressionEntry 2 1] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator scanRemainderRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def scanRemainderNonzeroBaseInput : Array Nat :=
  #[99, 7, 7, 88]

/-- At absolute base one, the visible values are right but the second `7`
incorrectly reuses origin one.  The prefix at base zero is deliberately
perfect, so a definition that forgot the `basekeys` offset would accept it. -/
private def scanRemainderNonzeroBaseWrongOriginState :
    MergeState (Occurrence Nat) PUnit :=
  { min_gallop := MIN_GALLOP
    listlen := 2
    basekeys := 1
    data :=
      { entries :=
          #[scanRemainderRegressionEntry 99 0,
            scanRemainderRegressionEntry 7 1,
            scanRemainderRegressionEntry 7 1,
            scanRemainderRegressionEntry 88 3] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator scanRemainderRegressionLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }
