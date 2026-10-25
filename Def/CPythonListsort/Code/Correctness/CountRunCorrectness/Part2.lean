/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/CountRunCorrectness.lean -/

import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part3
import Def.CPythonListsort.Code.Assembly.Order.Part4
import Structure.CPythonListsort.Code.Correctness.ReverseSliceCorrectness
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.DescendingRunNormalization
import Def.CPythonListsort.Code.Correctness.DescendingRunInvariant.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Correctness.ReverseRangeSupport
import Def.CPythonListsort.Code.Correctness.ScanRemainder.Part3
import Structure.CPythonListsort.Code.Correctness.CountRunCorrectness
/-!
# Functional correctness of `count_run`

This file proves that the actual bounded `countRun?` transcription returns a
nonempty sorted run, preserves whole key/payload entries, and preserves the
origin order of comparator-equivalent occurrences.  The public theorem is
tied to `countRunTraced?` through the reviewed `countRun_safe` exact-erasure
certificate; no second run detector is substituted for the transcribed one.

The descending case follows CPython's two-level reversal literally.  Equal
blocks are reversed as the scan discovers them, the final equal block is
reversed at the boundary, and then the complete descending prefix is
reversed.  Thus the temporary order inside equal blocks is not exposed by the
public postcondition.
-/


namespace CPythonListsort

universe u v w x

variable {alpha : Type u} {nu : Type v}

variable {beta : Type w} {rho : Type x}

/-! ## Concrete semantic regressions -/

def countRunCorrectnessOccurrence (value origin : Nat) :
    Occurrence Nat :=
  { value := value, origin := origin }

def countRunCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := countRunCorrectnessOccurrence value origin
    value := some payload }

def countRunCorrectnessState
    (slice : SortSlice (Occurrence Nat) Nat) :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def countRunCorrectnessTaggedEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 2 2 21,
        countRunCorrectnessEntry 1 3 10] }

def countRunCorrectnessAllEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 2 0 20,
        countRunCorrectnessEntry 2 1 21,
        countRunCorrectnessEntry 2 2 22] }

def countRunCorrectnessExtensionSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 1 2 10,
        countRunCorrectnessEntry 3 3 31,
        countRunCorrectnessEntry 4 4 40,
        countRunCorrectnessEntry 5 5 50,
        countRunCorrectnessEntry 0 6 0] }

def countRunCorrectnessNonzeroBaseSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 99 0 990,
        countRunCorrectnessEntry 3 1 30,
        countRunCorrectnessEntry 2 2 20,
        countRunCorrectnessEntry 1 3 10,
        countRunCorrectnessEntry 77 4 770] }

end CPythonListsort
