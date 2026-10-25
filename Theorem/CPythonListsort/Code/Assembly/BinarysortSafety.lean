/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/BinarysortSafety.lean -/

import Structure.CPythonListsort.Code.Assembly.SortSliceSafety
import Def.CPythonListsort.Code.Transcription.Binarysort.Part3
import Mathlib
import Structure.CPythonListsort.Code.Assembly.BinarysortSafety
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

namespace BinarysortTraceSafe

namespace BinarysortTraceMetadata

theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (hcurrent : BinarysortTraceMetadata current)
    (hnext : ∀ value, BinarysortTraceMetadata (next value)) :
    BinarysortTraceMetadata (current.bind next) := by
  cases hresult : current.result with
  | none =>
      constructor
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.fuel
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.noPushes
      · simpa [TraceResult.trace_bind, hresult] using hcurrent.tempLive
  | some value =>
      have hfollowing := hnext value
      constructor
      · simp [TraceResult.trace_bind, hresult, hcurrent.fuel,
          hfollowing.fuel]
      · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
          hcurrent.noPushes, hfollowing.noPushes]
      · rw [TraceResult.trace_bind, hresult,
          AccessTrace.tempPayloadAccessesLive_compose]
        exact ⟨hcurrent.tempLive, hfollowing.tempLive⟩

theorem copyKeys (destination source : SortSlice κ ν)
    (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.copyKeysFromTraced? destination source dst src) := by
  apply bind _ _ (keysRead source src)
  intro entry
  exact keysWrite destination dst entry

theorem copyValues (destination source : SortSlice κ ν)
    (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.copyValuesFromTraced? destination source dst src) := by
  apply bind _ _ (valuesRead source src)
  intro entry
  exact valuesWrite destination dst entry

end BinarysortTraceMetadata

theorem memmoveBackwardKeysTraced_metadata
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src) := by
  induction count generalizing slice with
  | zero => exact BinarysortTraceMetadata.pure slice
  | succ count ih =>
      apply BinarysortTraceMetadata.bind _ _
        (BinarysortTraceMetadata.copyKeys slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count))
      intro updated
      exact ih updated

theorem memmoveBackwardValuesTraced_metadata
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int) :
    BinarysortTraceMetadata
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src) := by
  induction count generalizing slice with
  | zero => exact BinarysortTraceMetadata.pure slice
  | succ count ih =>
      apply BinarysortTraceMetadata.bind _ _
        (BinarysortTraceMetadata.copyValues slice slice
          (dst + Int.ofNat count) (src + Int.ofNat count))
      intro updated
      exact ih updated

theorem memmoveBackwardKeysTraced_traceSafe
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst count)
    (hsrc : SortSlice.RangeInBounds slice src count) :
    ∃ updated,
      (SortSlice.memmoveBackwardKeysTraced? count slice dst src).result =
          some updated ∧
        BinarysortTraceSafe
          (SortSlice.memmoveBackwardKeysTraced? count slice dst src) ∧
        updated.entries.size = slice.entries.size := by
  rcases SortSlice.memmoveBackwardKeysTraced_safe count slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  rcases memmoveBackwardKeysTraced_metadata count slice dst src with
    ⟨hfuel, hpushes, hlive⟩
  exact ⟨updated, hresult, ⟨hfuel, hpushes, hbounds, hlive⟩, hsize⟩

theorem memmoveBackwardValuesTraced_traceSafe
    (count : Nat) (slice : SortSlice κ ν) (dst src : Int)
    (hdst : SortSlice.RangeInBounds slice dst count)
    (hsrc : SortSlice.RangeInBounds slice src count) :
    ∃ updated,
      (SortSlice.memmoveBackwardValuesTraced? count slice dst src).result =
          some updated ∧
        BinarysortTraceSafe
          (SortSlice.memmoveBackwardValuesTraced? count slice dst src) ∧
        updated.entries.size = slice.entries.size := by
  rcases SortSlice.memmoveBackwardValuesTraced_safe count slice dst src hdst hsrc with
    ⟨updated, hresult, hbounds, hsize⟩
  rcases memmoveBackwardValuesTraced_metadata count slice dst src with
    ⟨hfuel, hpushes, hlive⟩
  exact ⟨updated, hresult, ⟨hfuel, hpushes, hbounds, hlive⟩, hsize⟩

end BinarysortTraceSafe
end CPythonListsort
