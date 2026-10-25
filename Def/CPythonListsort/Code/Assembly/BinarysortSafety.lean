/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
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

/-- Traced binary-search phase.  A zero-fuel active interval marks exhaustion;
otherwise each iteration records exactly its midpoint key read before taking
the comparator-selected recursive branch. -/
def binarysortSearchTraced? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → SortSliceEntry κ ν →
      Nat → Nat → TraceResult BinarySearchResult
  | 0, _, _, _, _, left, right =>
      let result : BinarySearchResult :=
        { position := left, fuelExhausted := decide (left < right) }
      if left < right then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, lt, slice, base, pivot, left, right =>
      if left < right then
        let middle := (left + right) / 2
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat middle)).bind fun entry =>
            if iflt lt pivot.key entry.key then
              binarysortSearchTraced? fuel lt slice base pivot left middle
            else
              binarysortSearchTraced? fuel lt slice base pivot (middle + 1) right
      else
        TraceResult.pure { position := left, fuelExhausted := false }

/-- Key shift and pivot insertion, followed by the synchronized-values phase
when the explicit C pointer mode says that phase exists.  Each physical phase
starts from the same paired-store snapshot because either phase's primitive
erases to the transcription's single atomic paired movement. -/
def binarysortShiftInsertTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (ok position : Nat)
    (pivot : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  let count := ok - position
  let dst := base + Int.ofNat (position + 1)
  let src := base + Int.ofNat position
  let pivotIndex := base + Int.ofNat ok
  let insertIndex := base + Int.ofNat position
  (SortSlice.memmoveBackwardKeysTraced? count slice dst src).bind fun keyShifted =>
    (TraceResult.sortSliceKeysWrite? keyShifted insertIndex pivot).bind fun keyResult =>
      if valuesPresent then
        (TraceResult.sortSliceValuesRead? slice pivotIndex).bind fun valuePivot =>
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src).bind
            fun valueShifted =>
              TraceResult.sortSliceValuesWrite? valueShifted insertIndex valuePivot
      else
        TraceResult.pure keyResult

/-- Traced outer insertion loop. -/
def binarysortLoopTraced? :
    Nat → MergeState κ ν → SortSlice κ ν → Int → Nat → Nat →
      TraceResult (BinarysortResult κ ν)
  | 0, _, slice, _, n, ok =>
      let result : BinarysortResult κ ν :=
        { slice := slice, fuelExhausted := decide (ok < n) }
      if ok < n then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, state, slice, base, n, ok =>
      if ok < n then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat ok)).bind fun pivot =>
            (binarysortSearchTraced? (ok + 1) state.key_compare slice base pivot
              0 ok).bind fun search =>
                if search.fuelExhausted then
                  TraceResult.pure { slice := slice, fuelExhausted := true }
                else
                  (binarysortShiftInsertTraced? state.a.hasValues slice base ok
                    search.position pivot).bind fun updated =>
                      binarysortLoopTraced? fuel state updated base n (ok + 1)
      else
        TraceResult.pure { slice := slice, fuelExhausted := false }

/-- Fully traced binary insertion sort, with the same assertion-domain guard
and `ok = 0` normalization as the reviewed transcription. -/
def binarysortTraced? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (n ok : Nat) : TraceResult (BinarysortResult κ ν) :=
  if 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat then
    let ok := if ok = 0 then 1 else ok
    binarysortLoopTraced? n state slice base n ok
  else
    TraceResult.failure

end CPythonListsort
