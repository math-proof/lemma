/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/SortSliceSafety.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Mathlib
import Theorem.CPythonListsort.Code.Assembly.SortSliceSafety.Part2
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

end SortSlice
end CPythonListsort
