/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeHi.lean -/

import Def.CPythonListsort.Code.Transcription.Gallop.Part2
import Def.CPythonListsort.Code.Transcription.MergeMemory.Part3
import Structure.CPythonListsort.Code.Transcription.MergeHi.Part4
/-!
# Right-to-left stable merge transcription

This module transcribes CPython's `merge_hi` from the pinned
`Objects/listobject.c`.  The active list remains in `MergeState.data`; the
shorter right run is copied into `MergeState.a`, whose optional cells retain
the distinction between allocated and initialized temporary storage.

The ordinary and galloping loops are represented by a fuel-bounded phase
machine.  Modeled assertion or bounds failures return `none`.  Exhaustion of
the explicit loop or of a nested gallop is instead observable through
`fuelExhausted`, while rejection by `merge_getmem` retains C's `-1` result.

Equality selects B while filling backward, leaving the equal A entry before it
in final forward order.  Galloping retains C's `na == 0` and `nb == 0` branches
for inconsistent but total comparators, including the `na - k` and `nb - k`
conversions from insertion indices to backward block lengths.

Version one has no comparator-error result.  CPython's comparator-error jumps
to `Fail` are deliberately absent, while the temp-to-data copyback shared by
C's `Succeed` and `Fail` labels remains on successful exits.  Distinct
temp/data block copies model `sortslice_memcpy`; blocks moved within `data` use
overlap-safe `SortSlice.memmove?`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

def mergeHiLayoutFrame (state : MergeState κ ν) : MergeHiLayoutFrame :=
  { listlen := state.listlen
    basekeys := state.basekeys
    dataSize := state.data.entries.size
    pending := state.pending }

def mergeHiGallopStabilityRegressionState : MergeState Nat Nat :=
  { min_gallop := 1
    listlen := 7
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 2, value := some 20 },
            { key := 4, value := some 40 },
            { key := 6, value := some 60 },
            { key := 8, value := some 80 },
            { key := 1, value := some 11 },
            { key := 4, value := some 41 },
            { key := 5, value := some 51 }] }
    a :=
      { cells := Array.replicate 3 none
        backing := .inline
        hasValues := true }
    alloced := 3
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-! The next regression uses the non-irreflexive comparator `(· ≥ ·)`.  Its
second gallop consumes the whole temporary B run, after which the real loop
dispatcher reaches `mergeHiSucceed?` through its `nb = 0` guard.  A strict-`<`
control on the identical valid geometry returns the other insertion endpoint. -/

def mergeHiNbZeroHedgeRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 3, value := some 30 },
            { key := 99, value := some 99 },
            { key := 98, value := some 98 }] }
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

def mergeHiNbZeroHedgeRegressionCursor : MergeHiCursor Nat Nat :=
  { state := mergeHiNbZeroHedgeRegressionState
    dest := 2
    ssa := 0
    ssb := 1
    basea := 0
    na := 1
    nb := 2
    minGallop := MIN_GALLOP
    phase := .galloping 0 0 }

def mergeHiNbZeroHedgeStrictControlState : MergeState Nat Nat :=
  { mergeHiNbZeroHedgeRegressionState with
    key_compare := fun left right => decide (left < right) }

def mergeHiNbZeroHedgeStrictControlCursor : MergeHiCursor Nat Nat :=
  { mergeHiNbZeroHedgeRegressionCursor with
    state := mergeHiNbZeroHedgeStrictControlState }

end CPythonListsort
