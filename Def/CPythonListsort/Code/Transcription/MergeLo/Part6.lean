/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeLo.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Transcription.MergeLo.Part3
/-!
# Left-to-right merge transcription

This module transcribes CPython's `merge_lo`.  The main list remains in
`MergeState.data`; the shorter left run is copied into `MergeState.a` before
the merge starts.  Invalid assertion inputs, failed modeled accesses, and
invalid nested gallop calls return `none`.  The allocation guard and bounded
loop exhaustion remain observable and distinct in `MergeLoResult`.

The ordinary and galloping loops are represented by an explicit phase
machine.  Every recursive step consumes at least one live run entry, so the
input-size fuel is exposed only through the result flag and not as a caller
parameter.  Equality selects A while merging forward.  Galloping preserves
the C branch where an inconsistent but total comparator can consume all of A.

Version one has a pure Boolean comparator, so CPython's comparator-error jumps
to `Fail` and their negative result are deliberately absent.  The physical
temp-to-data copyback shared by C's `Succeed` and `Fail` labels remains on the
successful path.  Distinct temp/data block copies model `sortslice_memcpy`;
blocks moved within `data` use overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

def mergeLoLayoutFrame (state : MergeState κ ν) : MergeLoLayoutFrame :=
  { listlen := state.listlen
    basekeys := state.basekeys
    dataSize := state.data.entries.size
    pending := state.pending }

/-! Public executable regressions pin the ordinary-mode argument order and
stable equality branch. -/

def mergeLoStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 5
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 2, value := some 20 },
            { key := 3, value := some 32 },
            { key := 3, value := some 33 }] }
    a :=
      { cells := Array.replicate 2 none
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeLoGallopStabilityRegressionState : MergeState Nat Nat :=
  { mergeLoStabilityRegressionState with
    min_gallop := 1
    listlen := 6
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 4, value := some 40 },
            { key := 5, value := some 50 },
            { key := 1, value := some 10 },
            { key := 2, value := some 20 },
            { key := 3, value := some 31 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3 }

/-! The next regression deliberately uses the non-irreflexive comparator
`(· ≥ ·)`.  Its continuation always fails, so the successful result is an
observable witness that the first gallop's `index = na` result took the
`na = 0` Succeed hedge rather than continuing the round.  A strict-`<` control
on the identical geometry returns index zero and a different final ordering. -/

def mergeLoNaZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 99, value := some 99 },
            { key := 98, value := some 98 },
            { key := 0, value := some 0 }] }
    a :=
      { cells :=
          #[(some { key := 1, value := some 10 }),
            (some { key := 2, value := some 20 })]
        backing := .inline
        hasValues := true }
    alloced := 2
    pending := #[]
    key_compare := fun left right => decide (left ≥ right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def mergeLoNaZeroHedgeRegressionMachine : MergeLoMachine Nat Nat :=
  { state := mergeLoNaZeroHedgeRegressionState
    dest := 0
    aPos := 0
    bPos := 2
    na := 2
    nb := 1
    minGallop := MIN_GALLOP }

def mergeLoNaZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeLoNaZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeLoNaZeroHedgeStrictControlMachine : MergeLoMachine Nat Nat :=
  { mergeLoNaZeroHedgeRegressionMachine with
    state := mergeLoNaZeroHedgeStrictControlState }

end CPythonListsort
