/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/ScanRemainder.lean -/

import Def.CPythonListsort.Code.Correctness.PendingRunCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
import Mathlib
import Structure.CPythonListsort.Code.Correctness.ScanRemainder
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

namespace ScanRemainderMatches

/-! ## Initialization and anti-vacuity regressions -/

/-- Canonically tagged unkeyed input used by the occurrence-carrying
correctness execution. -/
def occurrenceInputSlice (input : Array α) : SortSlice (Occurrence α) PUnit :=
  { entries := (tagOccurrences input).map fun key =>
      { key := key, value := none } }

def scanRemainderRegressionLt : BoolComparator Nat :=
  fun left right => decide (left < right)

def scanRemainderRegressionEntry (value origin : Nat) :
    SortSliceEntry (Occurrence Nat) PUnit :=
  { key := { value := value, origin := origin }, value := none }

def scanRemainderRegressionInput : Array Nat :=
  #[1, 2]

/-- Empty pending coverage at `scanned = 0`, but with a deliberately corrupted
first unscanned key. -/
def scanRemainderWrongSuffixState :
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

def scanRemainderNonzeroBaseInput : Array Nat :=
  #[99, 7, 7, 88]

/-- At absolute base one, the visible values are right but the second `7`
incorrectly reuses origin one.  The prefix at base zero is deliberately
perfect, so a definition that forgot the `basekeys` offset would accept it. -/
def scanRemainderNonzeroBaseWrongOriginState :
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

end ScanRemainderMatches
end CPythonListsort
