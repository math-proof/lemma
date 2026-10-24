/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.AccessTrace
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

/-- Rejected same-backing overlap produces neither a partial access trace nor
an observable traced result, and still obeys exact erasure. -/
theorem memcpyTraced_sameBacking_overlap_rejected (valuesPresent : Bool)
    (count : Nat) (destination : SortSlice κ ν) (dst src : Int)
    (hoverlap : ¬ MemcpyRangesDisjoint dst src count) :
    (memcpyTraced? valuesPresent count destination .sameBacking dst src).result = none ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
        AccessTrace.empty ∧
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
        memcpy? count destination .sameBacking dst src := by
  simp [memcpyTraced?, memcpy?, MemcpySource.Admissible, hoverlap,
    TraceResult.failure, TraceResult.erase]

/-- The exact key-array event pair for one source-language assignment. -/
def keyCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .inputKeys,
     index := src, extent := sourceExtent },
   { kind := .write, region := .inputKeys,
     index := dst, extent := destinationExtent }]

/-- The exact optional-values event pair for one source-language assignment. -/
def valuesCopyAccesses (destinationExtent sourceExtent : Nat)
    (dst src : Int) : List AccessEvent :=
  [{ kind := .read, region := .synchronizedValues,
     index := src, extent := sourceExtent },
   { kind := .write, region := .synchronizedValues,
     index := dst, extent := destinationExtent }]

/-- The explicit displacement bounds imply validity of the advanced cursor. -/
theorem CursorMovementInRange.result
    {slice : SortSlice κ ν} {index amount : Int}
    (h : CursorMovementInRange slice index amount) :
    CursorInRange slice (advance index amount) := by
  rcases h with ⟨hcursor, hlower, hupper⟩
  rcases hcursor with ⟨hindex, _⟩
  simp only [CursorInRange, advance]
  constructor <;> omega

/-! ## Umbrella contract -/

/-- The complete public contract represented by the roadmap's
`sortslice-safe` node.  It bundles erasure for every movement primitive,
source-order facts under a global explicit-values-mode invariant, in-bounds
execution under exact cell/range premises, cursor validity (including only the
documented one-past endpoint), mode preservation, and common-extent
preservation on every successful array-mutating result. -/
structure SortSlicePrimitiveSafety (key : Type u) (value : Type v) : Prop where
  eraseCopyFrom : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromTraced? valuesPresent destination source dst src).erase =
      destination.copyFrom? source dst src
  eraseCopy : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyTraced? valuesPresent slice dst src).erase = slice.copy? dst src
  eraseCopyFromIncr : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromIncrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromIncr? source dst src
  eraseCopyFromDecr : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    (copyFromDecrTraced? valuesPresent destination source dst src).erase =
      destination.copyFromDecr? source dst src
  eraseCopyIncr : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyIncrTraced? valuesPresent slice dst src).erase =
      slice.copyIncr? dst src
  eraseCopyDecr : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    (copyDecrTraced? valuesPresent slice dst src).erase =
      slice.copyDecr? dst src
  eraseMemcpy : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    (memcpyTraced? valuesPresent count destination source dst src).erase =
      memcpy? count destination source dst src
  sameBackingMemcpyRejectsOverlap : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value) (dst src : Int),
    ¬ MemcpyRangesDisjoint dst src count →
      (memcpyTraced? valuesPresent count destination .sameBacking dst src).result =
          none ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).trace =
          AccessTrace.empty ∧
        (memcpyTraced? valuesPresent count destination .sameBacking dst src).erase =
          memcpy? count destination .sameBacking dst src
  eraseMemmoveFrom : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    (memmoveFromTraced? valuesPresent destination source dst src count).erase =
      memmoveFrom? destination source dst src count
  eraseMemmove : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (count : Nat),
    (memmoveTraced? valuesPresent slice dst src count).erase =
      slice.memmove? dst src count
  eraseAdvance : ∀ (valuesPresent : Bool) (index amount : Int),
    (advanceTraced valuesPresent index amount).erase =
      some (advance index amount)
  falseModeRejectsPayload : ∀ (entryKey : key) (entryValue : value),
    ¬ ValuesModeInvariant false
      ({ entries := #[{ key := entryKey, value := some entryValue }] } :
        SortSlice key value)
  copyEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  copyFromIncrEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromIncrTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  copyFromDecrEventOrder : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      (copyFromDecrTraced? valuesPresent destination source dst src).trace.accesses =
        keyCopyAccesses destination.entries.size source.entries.size dst src ++
          if valuesPresent then
            valuesCopyAccesses destination.entries.size source.entries.size dst src
          else []
  memcpyPhaseOrder : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      source.Admissible dst src count →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      (memcpyTraced? valuesPresent count destination source dst src).trace.accesses =
        (memcpyKeysTraced? count destination source.store dst src).trace.accesses ++
          if valuesPresent then
            (memcpyValuesTraced? count destination source.store dst src).trace.accesses
          else []
  memmoveFromPhaseOrder : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      (memmoveFromTraced? valuesPresent destination source dst src count).trace.accesses =
        match source with
        | .sameBacking =>
            match memmoveDirection dst src with
            | .forward =>
                (memmoveForwardKeysTraced? count destination dst src).trace.accesses ++
                  if valuesPresent then
                    (memmoveForwardValuesTraced? count destination dst src).trace.accesses
                  else []
            | .backward =>
                (memmoveBackwardKeysTraced? count destination dst src).trace.accesses ++
                  if valuesPresent then
                    (memmoveBackwardValuesTraced? count destination dst src).trace.accesses
                  else []
        | .distinctBacking source =>
            (memcpyKeysTraced? count destination source dst src).trace.accesses ++
              if valuesPresent then
                (memcpyValuesTraced? count destination source dst src).trace.accesses
              else []
  memmovePhaseOrder : ∀ (valuesPresent : Bool)
      (slice : SortSlice key value) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent slice →
      RangeInBounds slice dst count → RangeInBounds slice src count →
      (memmoveTraced? valuesPresent slice dst src count).trace.accesses =
        match memmoveDirection dst src with
        | .forward =>
            (memmoveForwardKeysTraced? count slice dst src).trace.accesses ++
              if valuesPresent then
                (memmoveForwardValuesTraced? count slice dst src).trace.accesses
              else []
        | .backward =>
            (memmoveBackwardKeysTraced? count slice dst src).trace.accesses ++
              if valuesPresent then
                (memmoveBackwardValuesTraced? count slice dst src).trace.accesses
              else []
  copyFromSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      ∃ updated,
          (copyFromTraced? valuesPresent destination source dst src).result =
            some updated ∧
          (copyFromTraced? valuesPresent destination source dst src).trace.allAccessesInBounds ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  copySafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      ∃ updated,
        (copyTraced? valuesPresent slice dst src).result = some updated ∧
          (copyTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          updated.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  copyFromIncrSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      ∃ result,
        (copyFromIncrTraced? valuesPresent destination source dst src).result =
            some result ∧
          ((copyFromIncrTraced? valuesPresent destination source dst src).trace
            |>.allAccessesInBounds) ∧
          result.slice.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          ValuesModeInvariant valuesPresent source ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange source result.src
  copyFromDecrSafety : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source →
      IndexInBounds destination dst → IndexInBounds source src →
      0 < dst → 0 < src →
      ∃ result,
        (copyFromDecrTraced? valuesPresent destination source dst src).result =
            some result ∧
          ((copyFromDecrTraced? valuesPresent destination source dst src).trace
            |>.allAccessesInBounds) ∧
          result.slice.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          ValuesModeInvariant valuesPresent source ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange source result.src
  copyIncrSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      ∃ result,
        (copyIncrTraced? valuesPresent slice dst src).result = some result ∧
          (copyIncrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          result.slice.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange result.slice result.src
  copyDecrSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int),
    ValuesModeInvariant valuesPresent slice →
      IndexInBounds slice dst → IndexInBounds slice src →
      0 < dst → 0 < src →
      ∃ result,
        (copyDecrTraced? valuesPresent slice dst src).result = some result ∧
          (copyDecrTraced? valuesPresent slice dst src).trace.allAccessesInBounds ∧
          result.slice.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent result.slice ∧
          CursorInRange result.slice result.dst ∧
          CursorInRange result.slice result.src
  memcpySafety : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (dst src : Int),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      source.Admissible dst src count →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      ∃ updated,
          (memcpyTraced? valuesPresent count destination source dst src).result =
            some updated ∧
          (memcpyTraced? valuesPresent count destination source dst src).trace.allAccessesInBounds ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  memmoveFromSafety : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent destination →
      ValuesModeInvariant valuesPresent source.store →
      RangeInBounds destination dst count →
      RangeInBounds source.store src count →
      ∃ updated,
        (memmoveFromTraced? valuesPresent destination source dst src count).result =
            some updated ∧
          ((memmoveFromTraced? valuesPresent destination source dst src count).trace
            |>.allAccessesInBounds) ∧
          updated.entries.size = destination.entries.size ∧
          ValuesModeInvariant valuesPresent updated ∧
          ValuesModeInvariant valuesPresent source.store
  memmoveSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (count : Nat),
    ValuesModeInvariant valuesPresent slice →
      RangeInBounds slice dst count → RangeInBounds slice src count →
      ∃ updated,
        (memmoveTraced? valuesPresent slice dst src count).result = some updated ∧
          (memmoveTraced? valuesPresent slice dst src count).trace.allAccessesInBounds ∧
          updated.entries.size = slice.entries.size ∧
          ValuesModeInvariant valuesPresent updated
  advanceSafety : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (index amount : Int),
    ValuesModeInvariant valuesPresent slice →
      CursorMovementInRange slice index amount →
      (advanceTraced valuesPresent index amount).result =
          some (advance index amount) ∧
        (advanceTraced valuesPresent index amount).trace = AccessTrace.empty ∧
        (advanceTraced valuesPresent index amount).trace.allAccessesInBounds ∧
        CursorInRange slice (advance index amount) ∧
        ValuesModeInvariant valuesPresent slice
  copyFromExtent : ∀ (valuesPresent : Bool)
      (destination source updated : SortSlice key value) (dst src : Int),
    (copyFromTraced? valuesPresent destination source dst src).result =
        some updated →
      updated.entries.size = destination.entries.size
  copyExtent : ∀ (valuesPresent : Bool)
      (slice updated : SortSlice key value) (dst src : Int),
    (copyTraced? valuesPresent slice dst src).result = some updated →
      updated.entries.size = slice.entries.size
  copyFromIncrExtent : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int)
      (result : CursorResult key value),
    (copyFromIncrTraced? valuesPresent destination source dst src).result =
        some result →
      result.slice.entries.size = destination.entries.size
  copyFromDecrExtent : ∀ (valuesPresent : Bool)
      (destination source : SortSlice key value) (dst src : Int)
      (result : CursorResult key value),
    (copyFromDecrTraced? valuesPresent destination source dst src).result =
        some result →
      result.slice.entries.size = destination.entries.size
  copyIncrExtent : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (result : CursorResult key value),
    (copyIncrTraced? valuesPresent slice dst src).result = some result →
      result.slice.entries.size = slice.entries.size
  copyDecrExtent : ∀ (valuesPresent : Bool) (slice : SortSlice key value)
      (dst src : Int) (result : CursorResult key value),
    (copyDecrTraced? valuesPresent slice dst src).result = some result →
      result.slice.entries.size = slice.entries.size
  memcpyExtent : ∀ (valuesPresent : Bool) (count : Nat)
      (destination : SortSlice key value)
      (source : MemcpySource destination) (updated : SortSlice key value)
      (dst src : Int),
    (memcpyTraced? valuesPresent count destination source dst src).result =
        some updated →
      updated.entries.size = destination.entries.size
  memmoveFromExtent : ∀ (valuesPresent : Bool)
      (destination : SortSlice key value)
      (source : MemmoveSource destination) (updated : SortSlice key value)
      (dst src : Int) (count : Nat),
    (memmoveFromTraced? valuesPresent destination source dst src count).result =
        some updated →
      updated.entries.size = destination.entries.size
  memmoveExtent : ∀ (valuesPresent : Bool)
      (slice updated : SortSlice key value) (dst src : Int) (count : Nat),
    (memmoveTraced? valuesPresent slice dst src count).result = some updated →
      updated.entries.size = slice.entries.size
