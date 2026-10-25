/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Mathlib
/-!
# Safety of the `sortslice` movement primitives

The instrumentation in this file is assembled directly from the typed
`SortSlice` access wrappers.  The Boolean `valuesPresent` is the modeled C
pointer mode: synchronized-values events are controlled only by that flag and
never by an individual entry's optional payload.

Bulk operations follow the source's two phases exactly: every key movement is
observed before any synchronized-values movement.  Each phase independently
executes the paired-entry transcription.  This is intentional: one execution
models movement of the key array and the other movement of the values array;
both erase to the same atomic paired-entry operation.
-/


namespace CPythonListsort

universe u v

namespace SortSlice

/-- An entry agrees with the explicit C `values != NULL` mode.  In values
mode every payload exists; without a values array every payload is absent. -/
def EntryMatchesValuesMode (valuesPresent : Bool)
    (entry : SortSliceEntry κ ν) : Prop :=
  match valuesPresent with
  | false => entry.value = none
  | true => ∃ value, entry.value = some value

/-- Global representation invariant connecting the separate C-pointer mode to
the paired-entry model.  The trace mode is never inferred from an individual
entry: instead, every entry must agree with the supplied mode. -/
def ValuesModeInvariant (valuesPresent : Bool) (slice : SortSlice κ ν) : Prop :=
  ∀ (index : Nat) (hindex : index < slice.entries.size),
    EntryMatchesValuesMode valuesPresent slice.entries[index]

/-- A signed index denotes an existing cell of `slice`. -/
def IndexInBounds (slice : SortSlice κ ν) (index : Int) : Prop :=
  0 ≤ index ∧ index < Int.ofNat slice.entries.size

/-- A pointer-like cursor lies between the beginning of the slice and its
permitted one-past endpoint, inclusive.  Unlike `IndexInBounds`, the upper
endpoint is a valid cursor but cannot itself be dereferenced. -/
def CursorInRange (slice : SortSlice κ ν) (cursor : Int) : Prop :=
  0 ≤ cursor ∧ cursor ≤ Int.ofNat slice.entries.size

/-- An `advance` starts at a valid cursor and its signed displacement stays
between the distance back to zero and the distance forward to the permitted
one-past endpoint.  This states the arithmetic obligation independently of
the desired postcondition even though advancement emits no indexed access. -/
def CursorMovementInRange (slice : SortSlice κ ν)
    (index amount : Int) : Prop :=
  CursorInRange slice index ∧
    -index ≤ amount ∧
    amount ≤ Int.ofNat slice.entries.size - index

/-- The half-open range `[start, start + count)` lies in `slice`.  For
`count = 0`, a one-past-the-end cursor is admitted. -/
def RangeInBounds (slice : SortSlice κ ν) (start : Int)
    (count : Nat) : Prop :=
  0 ≤ start ∧ start + Int.ofNat count ≤ Int.ofNat slice.entries.size

/-- One key-array copy, using the typed key read and key write wrappers. -/
def copyKeysFromTraced? (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  (TraceResult.sortSliceKeysRead? source src).bind fun entry =>
    TraceResult.sortSliceKeysWrite? destination dst entry

/-- One synchronized-values copy.  This primitive is called only when the
explicit C-pointer mode says that a values array is present. -/
def copyValuesFromTraced? (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  (TraceResult.sortSliceValuesRead? source src).bind fun entry =>
    TraceResult.sortSliceValuesWrite? destination dst entry

/-- Traced `sortslice_copy`: key read/write first, followed by values
read/write exactly when `valuesPresent` is true. -/
def copyFromTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν) (dst src : Int) :
    TraceResult (SortSlice κ ν) :=
  (copyKeysFromTraced? destination source dst src).bind fun keyResult =>
    if valuesPresent then
      copyValuesFromTraced? destination source dst src
    else
      TraceResult.pure keyResult

/-- Shared-store specialization of `copyFromTraced?`. -/
def copyTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (SortSlice κ ν) :=
  copyFromTraced? valuesPresent slice slice dst src

/-- Traced `sortslice_copy_incr` over its general two-slice C domain; cursor
movement occurs after the copy and only the destination store is updated. -/
def copyFromIncrTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  (copyFromTraced? valuesPresent destination source dst src).map fun updated =>
    { slice := updated, dst := dst + 1, src := src + 1 }

/-- Traced `sortslice_copy_decr` over its general two-slice C domain; cursor
movement occurs after the copy and only the destination store is updated. -/
def copyFromDecrTraced? (valuesPresent : Bool)
    (destination source : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  (copyFromTraced? valuesPresent destination source dst src).map fun updated =>
    { slice := updated, dst := dst - 1, src := src - 1 }

/-- Shared-store specialization of `copyFromIncrTraced?`. -/
def copyIncrTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  copyFromIncrTraced? valuesPresent slice slice dst src

/-- Shared-store specialization of `copyFromDecrTraced?`. -/
def copyDecrTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) : TraceResult (CursorResult κ ν) :=
  copyFromDecrTraced? valuesPresent slice slice dst src

/-- Key-array phase of `sortslice_memcpy`, in increasing address order. -/
def memcpyKeysTraced? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int →
      TraceResult (SortSlice κ ν)
  | 0, destination, _, _, _ => TraceResult.pure destination
  | count + 1, destination, source, dst, src =>
      (copyKeysFromTraced? destination source dst src).bind fun updated =>
        memcpyKeysTraced? count updated source (dst + 1) (src + 1)

/-- Synchronized-values phase of `sortslice_memcpy`, also increasing. -/
def memcpyValuesTraced? :
    Nat → SortSlice κ ν → SortSlice κ ν → Int → Int →
      TraceResult (SortSlice κ ν)
  | 0, destination, _, _, _ => TraceResult.pure destination
  | count + 1, destination, source, dst, src =>
      (copyValuesFromTraced? destination source dst src).bind fun updated =>
        memcpyValuesTraced? count updated source (dst + 1) (src + 1)

/-- Traced `sortslice_memcpy`.  The backing-domain check occurs before either
physical phase.  On an admissible call the second phase starts from the
original paired store, reflecting that C's key and values arrays are distinct. -/
def memcpyTraced? (valuesPresent : Bool) (count : Nat)
    (destination : SortSlice κ ν) (source : MemcpySource destination)
    (dst src : Int) :
    TraceResult (SortSlice κ ν) :=
  if source.Admissible dst src count then
    (memcpyKeysTraced? count destination source.store dst src).bind fun keyResult =>
      if valuesPresent then
        memcpyValuesTraced? count destination source.store dst src
      else
        TraceResult.pure keyResult
  else
    TraceResult.failure

/-- Forward key phase of an overlap-safe move. -/
def memmoveForwardKeysTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      (copyKeysFromTraced? slice slice dst src).bind fun updated =>
        memmoveForwardKeysTraced? count updated (dst + 1) (src + 1)

/-- Forward synchronized-values phase of an overlap-safe move. -/
def memmoveForwardValuesTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      (copyValuesFromTraced? slice slice dst src).bind fun updated =>
        memmoveForwardValuesTraced? count updated (dst + 1) (src + 1)

/-- Backward key phase.  The first event is at offset `count`, matching the
source-safe right-to-left traversal in the transcription. -/
def memmoveBackwardKeysTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      let offset := Int.ofNat count
      (copyKeysFromTraced? slice slice (dst + offset) (src + offset)).bind
        fun updated => memmoveBackwardKeysTraced? count updated dst src

/-- Backward synchronized-values phase, with the identical overlap order. -/
def memmoveBackwardValuesTraced? :
    Nat → SortSlice κ ν → Int → Int → TraceResult (SortSlice κ ν)
  | 0, slice, _, _ => TraceResult.pure slice
  | count + 1, slice, dst, src =>
      let offset := Int.ofNat count
      (copyValuesFromTraced? slice slice (dst + offset) (src + offset)).bind
        fun updated => memmoveBackwardValuesTraced? count updated dst src

/-- Traced overlap-safe movement.  Both key and values phases use the same
direction selected by `memmoveDirection`; all key events precede value events. -/
def memmoveTraced? (valuesPresent : Bool) (slice : SortSlice κ ν)
    (dst src : Int) (count : Nat) : TraceResult (SortSlice κ ν) :=
  match memmoveDirection dst src with
  | .forward =>
      (memmoveForwardKeysTraced? count slice dst src).bind fun keyResult =>
        if valuesPresent then
          memmoveForwardValuesTraced? count slice dst src
        else
          TraceResult.pure keyResult
  | .backward =>
      (memmoveBackwardKeysTraced? count slice dst src).bind fun keyResult =>
      if valuesPresent then
          memmoveBackwardValuesTraced? count slice dst src
        else
          TraceResult.pure keyResult

/-- Traced general two-store `sortslice_memmove`.  Explicit same-backing
provenance selects the overlap-safe directional trace, while explicit distinct
provenance selects increasing-address key and values phases over the unchanged
source store. -/
def memmoveFromTraced? (valuesPresent : Bool)
    (destination : SortSlice κ ν) (source : MemmoveSource destination)
    (dst src : Int) (count : Nat) : TraceResult (SortSlice κ ν) :=
  match source with
  | .sameBacking => memmoveTraced? valuesPresent destination dst src count
  | .distinctBacking source =>
      (memcpyKeysTraced? count destination source dst src).bind fun keyResult =>
        if valuesPresent then
          memcpyValuesTraced? count destination source dst src
        else
          TraceResult.pure keyResult

/-- Pointer advancement emits no indexed access.  `valuesPresent` remains an
explicit input because C advances the optional values pointer in the same
mode, but both pointer adjustments erase to the model's single cursor. -/
def advanceTraced (_valuesPresent : Bool) (index amount : Int) :
    TraceResult Int :=
  TraceResult.pure (advance index amount)

end SortSlice
end CPythonListsort
