/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ReverseSliceSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.ReverseSlice
import Inductive.CPythonListsort.Code.Assembly.ReverseSliceSafety
/-!
# Slice-reversal safety

This module instruments the two physical phases of CPython's
`sortslice_reverse`.  A key phase is always executed; a synchronized-values
phase is executed from the same pre-state exactly when the explicit values
mode is enabled.  Each phase performs the reviewed reversal itself through
typed access wrappers, so the trace is produced by execution rather than
attached to an independently computed result.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseSlicePhase

def readTraced? (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
    (index : Int) : TraceResult (SortSliceEntry κ ν) :=
  match phase with
  | .keys => TraceResult.sortSliceKeysRead? slice index
  | .values => TraceResult.sortSliceValuesRead? slice index

def writeTraced? (phase : ReverseSlicePhase) (slice : SortSlice κ ν)
    (index : Int) (entry : SortSliceEntry κ ν) : TraceResult (SortSlice κ ν) :=
  match phase with
  | .keys => TraceResult.sortSliceKeysWrite? slice index entry
  | .values => TraceResult.sortSliceValuesWrite? slice index entry

def reverseSliceResult (slice : SortSlice κ ν)
    (fuelExhausted : Bool) : ReverseSliceResult κ ν :=
  { slice := slice, fuelExhausted := fuelExhausted }

/-- One genuinely instrumented physical `reverse_slice` loop. -/
def reverseSlicePhaseLoopTraced? :
    Nat → ReverseSlicePhase → SortSlice κ ν → Int → Int →
      TraceResult (ReverseSliceResult κ ν)
  | 0, _, slice, lo, hi =>
      let result := reverseSliceResult slice (decide (lo < hi))
      if lo < hi then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, phase, slice, lo, hi =>
      if lo < hi then
        (phase.readTraced? slice lo).bind fun left =>
          (phase.readTraced? slice hi).bind fun right =>
            (phase.writeTraced? slice lo right).bind fun afterLeft =>
              (phase.writeTraced? afterLeft hi left).bind fun afterRight =>
                reverseSlicePhaseLoopTraced? fuel phase afterRight
                  (lo + 1) (hi - 1)
      else
        TraceResult.pure (reverseSliceResult slice false)

/-- Traced half-open `reverse_slice` for one physical array.

The returned `SortSlice` is the paired-snapshot semantic update for that
physical phase, not a literal intermediate C store.  In particular, callers
that instrument both key and values phases must run each phase from the same
pre-state and compose their traces; they must not feed the key-phase result to
the values phase. -/
def reverseSlicePhaseTraced? (phase : ReverseSlicePhase)
    (slice : SortSlice κ ν) (lo hi : Int) :
    TraceResult (ReverseSliceResult κ ν) :=
  if lo ≤ hi then
    if lo < hi then
      reverseSlicePhaseLoopTraced? (hi - lo).toNat phase slice lo (hi - 1)
    else
      TraceResult.pure (reverseSliceResult slice false)
  else
    TraceResult.failure

/-- Public key-array specialization of the traced `reverse_slice`. -/
def reverseSliceTraced? (slice : SortSlice κ ν) (lo hi : Int) :
    TraceResult (ReverseSliceResult κ ν) :=
  reverseSlicePhaseTraced? .keys slice lo hi

/-- Traced `sortslice_reverse`: complete key reversal first, then the complete
synchronized-values reversal from the same pre-state when values are present.
Both phases execute the paired snapshot update; the second phase's result is
the same reviewed reversal, while its events represent the second C array. -/
def sortsliceReverseTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (n : Nat) :
    TraceResult (ReverseSliceResult κ ν) :=
  let hi := base + Int.ofNat n
  (reverseSlicePhaseTraced? .keys slice base hi).bind fun keyResult =>
    if valuesPresent then
      reverseSlicePhaseTraced? .values slice base hi
    else
      TraceResult.pure keyResult

end ReverseSlicePhase
end CPythonListsort
