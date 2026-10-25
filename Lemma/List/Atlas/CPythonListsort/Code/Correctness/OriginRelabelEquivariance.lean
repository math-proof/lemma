import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
open CPythonListsort


namespace CPythonListsort

/--
[mirrorOrigin_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOrigin_of_lt
  {alpha : Type u}
  {nu : Type v}
  {size origin : Nat}
-- given
  (h : origin < size) :
-- imply
  mirrorOrigin size origin = size - 1 - origin := by
-- proof
  simp [mirrorOrigin, h]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOrigin_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOrigin_involutive
  {alpha : Type u}
  {nu : Type v}
  {size origin : Nat} :
-- imply
  mirrorOrigin size (mirrorOrigin size origin) = origin := by
-- proof
  by_cases h : origin < size
  · have hmirror : size - 1 - origin < size := by omega
    simp [mirrorOrigin, h, hmirror]
    omega
  · simp [mirrorOrigin, h]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOccurrence_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOccurrence_value
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : Occurrence alpha} :
-- imply
  (mirrorOccurrence size entry).value = entry.value :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOccurrence_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOccurrence_origin
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : Occurrence alpha} :
-- imply
  (mirrorOccurrence size entry).origin = mirrorOrigin size entry.origin :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOccurrence_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOccurrence_involutive
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : Occurrence alpha} :
-- imply
  mirrorOccurrence size (mirrorOccurrence size entry) = entry := by
-- proof
  cases entry
  simp [mirrorOccurrence]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSliceEntry_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSliceEntry_key
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (mirrorSortSliceEntry size entry).key = mirrorOccurrence size entry.key :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSliceEntry_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSliceEntry_value
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (mirrorSortSliceEntry size entry).value = entry.value :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSliceEntry_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSliceEntry_involutive
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  mirrorSortSliceEntry size (mirrorSortSliceEntry size entry) = entry := by
-- proof
  cases entry
  simp [mirrorSortSliceEntry]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_involutive
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  mirrorSortSlice size (mirrorSortSlice size slice) = slice := by
-- proof
  cases slice with
  | mk entries =>
    simp only [mirrorSortSlice, Array.map_map]
    simp [Function.comp_def]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorTempStorage_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorTempStorage_involutive
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {storage : TempStorage (Occurrence alpha) nu} :
-- imply
  mirrorTempStorage size (mirrorTempStorage size storage) = storage := by
-- proof
  cases storage with
  | mk cells backing hasValues =>
    simp [mirrorTempStorage, Array.map_map, Function.comp_def]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_involutive
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  mirrorMergeState size (mirrorMergeState size state) = state := by
-- proof
  cases state
  simp [mirrorMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_entries_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_entries_size
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  (mirrorSortSlice size slice).entries.size = slice.entries.size := by
-- proof
  simp [mirrorSortSlice]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorTempStorage_cells_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorTempStorage_cells_size
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {storage : TempStorage (Occurrence alpha) nu} :
-- imply
  (mirrorTempStorage size storage).cells.size = storage.cells.size := by
-- proof
  simp [mirrorTempStorage]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_data_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_data_size
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).data.entries.size = state.data.entries.size := by
-- proof
  simp [mirrorMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_data
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).data = mirrorSortSlice size state.data :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[occurrenceComparator_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma occurrenceComparator_mirror
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {left right : Occurrence alpha} :
-- imply
  occurrenceComparator lt (mirrorOccurrence size left) (mirrorOccurrence size right) = occurrenceComparator lt left right := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[iflt_occurrenceComparator_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma iflt_occurrenceComparator_mirror
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {left right : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  iflt (occurrenceComparator lt) (mirrorSortSliceEntry size left).key (mirrorSortSliceEntry size right).key = iflt (occurrenceComparator lt) left.key right.key := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_read](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_read
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {index : Int} :
-- imply
  (mirrorSortSlice size slice).read? index = (slice.read? index).map (mirrorSortSliceEntry size) := by
-- proof
  by_cases hindex : 0 ≤ index <;>
    simp [mirrorSortSlice, SortSlice.read?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_write](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_write
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {index : Int}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (mirrorSortSlice size slice).write? index (mirrorSortSliceEntry size entry) = (slice.write? index entry).map (mirrorSortSlice size) := by
-- proof
  by_cases hindex : 0 ≤ index
  · by_cases hin : index.toNat < slice.entries.size
    · simp [mirrorSortSlice, mirrorSortSliceEntry, SortSlice.write?, hindex, hin]
    · simp [mirrorSortSlice, SortSlice.write?, hindex, hin]
  · simp [SortSlice.write?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_key_compare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_key_compare
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).key_compare = state.key_compare :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_pending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_pending
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).pending = state.pending :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_listlen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_listlen
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).listlen = state.listlen :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_basekeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_basekeys
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).basekeys = state.basekeys :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_alloced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_alloced
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).alloced = state.alloced :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorMergeState_minrunState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorMergeState_minrunState
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (mirrorMergeState size state).minrunState = state.minrunState :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copyFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copyFrom
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size destination).copyFrom? (mirrorSortSlice size source) dst src = (destination.copyFrom? source dst src).map (mirrorSortSlice size) := by
-- proof
  unfold SortSlice.copyFrom?
  rw [mirrorSortSlice_read]
  cases hread : source.read? src with
  | none => simp
  | some entry =>
    simp only [Option.map_some]
    exact mirrorSortSlice_write size destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copy
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size slice).copy? dst src = (slice.copy? dst src).map (mirrorSortSlice size) := by
-- proof
  simp [SortSlice.copy?, mirrorSortSlice_copyFrom]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copyFromIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copyFromIncr
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size destination).copyFromIncr? (mirrorSortSlice size source) dst src = (destination.copyFromIncr? source dst src).map (mirrorCursorResult size) := by
-- proof
  unfold SortSlice.copyFromIncr?
  rw [mirrorSortSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [mirrorCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copyFromDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copyFromDecr
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size destination).copyFromDecr? (mirrorSortSlice size source) dst src = (destination.copyFromDecr? source dst src).map (mirrorCursorResult size) := by
-- proof
  unfold SortSlice.copyFromDecr?
  rw [mirrorSortSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [mirrorCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copyIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copyIncr
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size slice).copyIncr? dst src = (slice.copyIncr? dst src).map (mirrorCursorResult size) := by
-- proof
  simp [SortSlice.copyIncr?, mirrorSortSlice_copyFromIncr]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_copyDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_copyDecr
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (mirrorSortSlice size slice).copyDecr? dst src = (slice.copyDecr? dst src).map (mirrorCursorResult size) := by
-- proof
  simp [SortSlice.copyDecr?, mirrorSortSlice_copyFromDecr]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_memcpyCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_memcpyCore
  {alpha : Type u}
  {nu : Type v}
  {size count : Nat}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memcpyCore? count (mirrorSortSlice size destination) (mirrorSortSlice size source) dst src = (SortSlice.memcpyCore? count destination source dst src).map (mirrorSortSlice size) := by
-- proof
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memcpyCore?]
    rw [mirrorSortSlice_copyFrom]
    cases hcopy : destination.copyFrom? source dst src with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_memmoveForward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_memmoveForward
  {alpha : Type u}
  {nu : Type v}
  {size count : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memmoveForward? count (mirrorSortSlice size slice) dst src = (SortSlice.memmoveForward? count slice dst src).map (mirrorSortSlice size) := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memmoveForward?]
    rw [mirrorSortSlice_copy]
    cases hcopy : slice.copy? dst src with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_memmoveBackward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_memmoveBackward
  {alpha : Type u}
  {nu : Type v}
  {size count : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memmoveBackward? count (mirrorSortSlice size slice) dst src = (SortSlice.memmoveBackward? count slice dst src).map (mirrorSortSlice size) := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memmoveBackward?]
    rw [mirrorSortSlice_copy]
    cases hcopy : slice.copy? (dst + Int.ofNat count) (src + Int.ofNat count) with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_memmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_memmove
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int}
  {count : Nat} :
-- imply
  (mirrorSortSlice size slice).memmove? dst src count = (slice.memmove? dst src count).map (mirrorSortSlice size) := by
-- proof
  simp only [SortSlice.memmove?]
  cases SortSlice.memmoveDirection dst src <;>
    simp [mirrorSortSlice_memmoveForward,
      mirrorSortSlice_memmoveBackward]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorReverseSliceLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorReverseSliceLoop
  {alpha : Type u}
  {nu : Type v}
  {size fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
-- given
  (lo hi : Int) :
-- imply
  reverseSliceLoop? fuel (mirrorSortSlice size slice) lo hi = (reverseSliceLoop? fuel slice lo hi).map (mirrorReverseSliceResult size) := by
-- proof
  induction fuel generalizing slice lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [reverseSliceLoop?]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      rw [mirrorSortSlice_read]
      cases hleft : slice.read? lo with
      | none => simp
      | some left =>
        simp only [Option.map_some]
        rw [mirrorSortSlice_read]
        cases hright : slice.read? hi with
        | none => simp
        | some right =>
          cases hwriteLeft : slice.write? lo right with
          | none => simp [hwriteLeft, mirrorSortSlice_write]
          | some afterLeft =>
            cases hwriteRight : afterLeft.write? hi left with
            | none =>
              simp [hwriteLeft, hwriteRight, mirrorSortSlice_write]
            | some afterRight =>
              simp [hwriteLeft, hwriteRight, mirrorSortSlice_write, ih]
    · simp [hactive, mirrorReverseSliceResult]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorReverseSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorReverseSlice
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
-- given
  (lo hi : Int) :
-- imply
  reverseSlice? (mirrorSortSlice size slice) lo hi = (reverseSlice? slice lo hi).map (mirrorReverseSliceResult size) := by
-- proof
  unfold reverseSlice?
  by_cases horder : lo ≤ hi
  · rw [if_pos horder, if_pos horder]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      exact mirrorReverseSliceLoop size (hi - lo).toNat slice lo (hi - 1)
    · simp [hactive, mirrorReverseSliceResult]
  · simp [horder]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortsliceReverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortsliceReverse
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {count : Nat} :
-- imply
  sortsliceReverse? (mirrorSortSlice size slice) base count = (sortsliceReverse? slice base count).map (mirrorReverseSliceResult size) := by
-- proof
  simp [sortsliceReverse?, mirrorReverseSlice]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorAscendingScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorAscendingScan
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n : Nat} :
-- imply
  ascendingScan? fuel (occurrenceComparator lt) (mirrorSortSlice size slice) base nremaining n = ascendingScan? fuel (occurrenceComparator lt) slice base nremaining n := by
-- proof
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [ascendingScan?]
    by_cases hscan : n < nremaining
    · rw [if_pos hscan, if_pos hscan]
      rw [mirrorSortSlice_read]
      cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
      | none => rfl
      | some previous =>
        simp only [Option.map_some, countRunBindOptionAcross]
        rw [mirrorSortSlice_read]
        cases hnext : slice.read? (base + Int.ofNat n) with
        | none => rfl
        | some next =>
          simp only [Option.map_some]
          rw [iflt_occurrenceComparator_mirror]
          split <;> simp [ih]
    · simp [hscan]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorReverseLastEqual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorReverseLastEqual
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n neq : Nat} :
-- imply
  reverseLastEqual? (mirrorSortSlice size slice) base n neq = (reverseLastEqual? slice base n neq).map (mirrorReverseEqualResult size) := by
-- proof
  unfold reverseLastEqual?
  by_cases heq : neq = 0
  · simp [heq, mirrorReverseEqualResult]
  · rw [if_neg heq, if_neg heq]
    dsimp only
    rw [mirrorSortsliceReverse]
    cases hreversed : sortsliceReverse? slice
      (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) with
    | none => simp
    | some reversed =>
      simp [mirrorReverseEqualResult, mirrorReverseSliceResult]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorDescendingScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorDescendingScan
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n neq : Nat} :
-- imply
  descendingScan? fuel (occurrenceComparator lt) (mirrorSortSlice size slice) base nremaining n neq = (descendingScan? fuel (occurrenceComparator lt) slice base nremaining n neq).map (mirrorDescendingScanResult size) := by
-- proof
  induction fuel generalizing slice n neq with
  | zero => rfl
  | succ fuel ih =>
    simp only [descendingScan?]
    by_cases hscan : n < nremaining
    · rw [if_pos hscan, if_pos hscan]
      rw [mirrorSortSlice_read]
      cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
      | none => simp
      | some previous =>
        simp only [Option.map_some]
        rw [mirrorSortSlice_read]
        cases hnext : slice.read? (base + Int.ofNat n) with
        | none => simp
        | some next =>
          by_cases hless :
            iflt (occurrenceComparator lt) next.key previous.key = true
          · simp only [iflt_eq] at hless
            simp only [iflt_eq]
            rw [mirrorReverseLastEqual]
            cases hreversed : reverseLastEqual? slice base n neq with
            | none => simp [hless]
            | some reversed =>
              cases hfuel : reversed.fuelExhausted <;>
                simp [hless, hfuel, mirrorReverseEqualResult,
                  mirrorDescendingScanResult, ih]
          · by_cases hgreater :
            iflt (occurrenceComparator lt) previous.key next.key = true
            · simp only [iflt_eq] at hless hgreater
              simp [iflt_eq, hless, hgreater, mirrorDescendingScanResult]
            · simp only [iflt_eq] at hless hgreater
              simp [iflt_eq, hless, hgreater, ih]
    · simp [hscan, mirrorDescendingScanResult]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorFinishDescending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorFinishDescending
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  finishDescending? (mirrorMergeState size state) (mirrorSortSlice size slice) base nremaining n = (finishDescending? state slice base nremaining n).map (mirrorCountRunResult size) := by
-- proof
  unfold finishDescending?
  simp only [mirrorMergeState_key_compare, hcompare]
  rw [mirrorDescendingScan]
  cases hdescending : descendingScan? nremaining (occurrenceComparator lt) slice
    base nremaining n 0 with
  | none => simp
  | some descending =>
    by_cases hfuel : descending.fuelExhausted = true
    · simp [hfuel, mirrorDescendingScanResult, mirrorCountRunResult]
    · cases hequal : reverseLastEqual? descending.slice base descending.length
      descending.equalTail with
      | none =>
        simp [hfuel, hequal, mirrorDescendingScanResult]
      | some equalReversed =>
        by_cases hequalFuel : equalReversed.fuelExhausted = true
        · simp [hfuel, hequal, hequalFuel, mirrorDescendingScanResult,
          mirrorReverseEqualResult, mirrorCountRunResult]
        · cases hwhole : sortsliceReverse? equalReversed.slice base
          descending.length with
          | none =>
            simp [hfuel, hequal, hequalFuel, hwhole,
              mirrorDescendingScanResult, mirrorReverseEqualResult]
          | some wholeReversed =>
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · simp [hfuel, hequal, hequalFuel, hwhole, hwholeFuel,
              mirrorDescendingScanResult, mirrorReverseEqualResult,
              mirrorReverseSliceResult, mirrorCountRunResult]
            · simp only [hfuel, Bool.false_eq_true, if_false,
              Option.map_some, Option.bind_eq_bind, Option.bind_some,
              mirrorDescendingScanResult_fuel,
              mirrorDescendingScanResult_slice,
              mirrorDescendingScanResult_length,
              mirrorDescendingScanResult_equalTail]
              rw [mirrorReverseLastEqual]
              simp only [hequal, Option.map_some, Option.bind_some,
                mirrorReverseEqualResult_fuel,
                mirrorReverseEqualResult_slice, hequalFuel,
                Bool.false_eq_true, if_false]
              rw [mirrorSortsliceReverse]
              simp only [hwhole, Option.map_some, Option.bind_some,
                mirrorReverseSliceResult, hwholeFuel,
                Bool.false_eq_true, if_false]
              rw [mirrorAscendingScan]
              cases hascending : ascendingScan? nremaining
                (occurrenceComparator lt) wholeReversed.slice base
                nremaining descending.length <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorCountRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorCountRun
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  countRun? (mirrorMergeState size state) (mirrorSortSlice size slice) base nremaining = (countRun? state slice base nremaining).map (mirrorCountRunResult size) := by
-- proof
  unfold countRun?
  simp only [mirrorMergeState_key_compare, hcompare]
  by_cases hvalid : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hvalid, if_pos hvalid, mirrorAscendingScan]
    cases hascending : ascendingScan? nremaining (occurrenceComparator lt) slice
      base nremaining 1 with
    | none => simp [countRunBindOptionAcross]
    | some ascending =>
      cases hfuel : ascending.fuelExhausted with
      | true => simp [countRunBindOptionAcross, hfuel, mirrorCountRunResult]
      | false =>
        by_cases hcomplete : ascending.length = nremaining
        · simp [countRunBindOptionAcross, hfuel, hcomplete,
          mirrorCountRunResult]
        · by_cases hlong : 1 < ascending.length
          · simp only [countRunBindOptionAcross, hfuel,
            Bool.false_eq_true, if_false, hcomplete, hlong, if_true]
            rw [mirrorSortSlice_read]
            cases hfirst : slice.read? base with
            | none => simp
            | some first =>
              simp only [Option.map_some]
              rw [mirrorSortSlice_read]
              cases hlast : slice.read? (base + Int.ofNat (ascending.length - 1)) with
              | none => simp
              | some last =>
                simp only [Option.map_some]
                by_cases hordered :
                  occurrenceComparator lt first.key last.key = true
                · simp [hordered, iflt, mirrorCountRunResult]
                · cases hreversed : sortsliceReverse? slice base
                  ascending.length with
                  | none => simp [hordered, iflt, hreversed]
                  | some reversed =>
                    cases hreverseFuel : reversed.fuelExhausted with
                    | true => simp [hordered, iflt, hreversed,
                      hreverseFuel, mirrorReverseSliceResult,
                      mirrorCountRunResult]
                    | false =>
                      simp [hordered, iflt, hreversed, hreverseFuel,
                        mirrorReverseSliceResult,
                        mirrorFinishDescending lt size state
                          reversed.slice base nremaining
                          (ascending.length + 1) hcompare]
          · simp only [countRunBindOptionAcross, hfuel,
            Bool.false_eq_true, if_false, hcomplete, hlong]
            exact mirrorFinishDescending lt size state slice base nremaining
              (ascending.length + 1) hcompare
  · simp [hvalid]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorBinarysortSearch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorBinarysortSearch
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {pivot : SortSliceEntry (Occurrence alpha) nu}
  {left right : Nat} :
-- imply
  binarysortSearch? fuel (occurrenceComparator lt) (mirrorSortSlice size slice) base (mirrorSortSliceEntry size pivot) left right = binarysortSearch? fuel (occurrenceComparator lt) slice base pivot left right := by
-- proof
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
    simp only [binarysortSearch?]
    by_cases hsearch : left < right
    · rw [if_pos hsearch, if_pos hsearch, mirrorSortSlice_read]
      cases hread : slice.read? (base + Int.ofNat ((left + right) / 2)) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, binarysortBindOptionAcross]
        rw [iflt_occurrenceComparator_mirror]
        split <;> simp [ih]
    · simp [hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorBinarysortLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorBinarysortLoop
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n ok : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  binarysortLoop? fuel (mirrorMergeState size state) (mirrorSortSlice size slice) base n ok = (binarysortLoop? fuel state slice base n ok).map (mirrorBinarysortResult size) := by
-- proof
  induction fuel generalizing slice ok with
  | zero => rfl
  | succ fuel ih =>
    simp only [binarysortLoop?]
    by_cases hloop : ok < n
    · rw [if_pos hloop, if_pos hloop, mirrorSortSlice_read]
      cases hpivot : slice.read? (base + Int.ofNat ok) with
      | none => simp [binarysortBindOptionAcross]
      | some pivot =>
        simp only [Option.map_some, binarysortBindOptionAcross]
        simp only [mirrorMergeState_key_compare, hcompare]
        rw [mirrorBinarysortSearch]
        cases hsearch : binarysortSearch? (ok + 1) (occurrenceComparator lt)
          slice base pivot 0 ok with
        | none => simp
        | some search =>
          cases hfuel : search.fuelExhausted with
          | true => simp [hfuel, mirrorBinarysortResult]
          | false =>
            simp only [hfuel,
              Bool.false_eq_true, if_false]
            rw [mirrorSortSlice_memmove]
            cases hmove : slice.memmove?
              (base + Int.ofNat (search.position + 1))
              (base + Int.ofNat search.position) (ok - search.position) with
            | none => simp
            | some moved =>
              simp only [Option.map_some, Int.ofNat_eq_natCast,
                Option.bind_eq_bind, Option.bind_some,
                mirrorSortSlice_write, Option.map_bind,
                Function.comp_apply]
              rw [Option.bind_map]
              apply Option.bind_congr
              intro inserted _
              exact ih inserted (ok + 1)
    · rw [if_neg hloop, if_neg hloop]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[mirrorBinarysort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorBinarysort
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n ok : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  binarysort? (mirrorMergeState size state) (mirrorSortSlice size slice) base n ok = (binarysort? state slice base n ok).map (mirrorBinarysortResult size) := by
-- proof
  unfold binarysort?
  by_cases hvalid : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hvalid, if_pos hvalid]
    split <;> apply mirrorBinarysortLoop lt size n state slice base n <;>
      exact hcompare
  · simp [hvalid]

end CPythonListsort

namespace CPythonListsort

/--
[mirrorSortSlice_entries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorSortSlice_entries
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  (mirrorSortSlice size slice).entries = slice.entries.map (mirrorSortSliceEntry size) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeEntries_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma sortSliceRangeEntries_mirror
  {alpha : Type u}
  {nu : Type v}
  {size start count : Nat}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  sortSliceRangeEntries (mirrorSortSlice size slice) start count = (sortSliceRangeEntries slice start count).map (mirrorSortSliceEntry size) := by
-- proof
  simp [sortSliceRangeEntries, mirrorSortSlice, Array.map_extract]

end CPythonListsort

namespace CPythonListsort

/--
[sortSliceRangeKeys_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma sortSliceRangeKeys_mirror
  {alpha : Type u}
  {nu : Type v}
  {size start count : Nat}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  sortSliceRangeKeys (mirrorSortSlice size slice) start count = (sortSliceRangeKeys slice start count).map (mirrorOccurrence size) := by
-- proof
  simp [sortSliceRangeKeys, Array.map_map, Function.comp_def]

end CPythonListsort

namespace CPythonListsort

/--
[pendingRunOccurrenceKeys_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma pendingRunOccurrenceKeys_mirror
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {run : PendingRun} :
-- imply
  pendingRunOccurrenceKeys (mirrorMergeState size state) run = (pendingRunOccurrenceKeys state run).map (mirrorOccurrence size) := by
-- proof
  change sortSliceRangeKeys (mirrorSortSlice size state.data) run.base
    run.len.toNat =
    (sortSliceRangeKeys state.data run.base run.len.toNat).map
      (mirrorOccurrence size)
  exact sortSliceRangeKeys_mirror size run.base run.len.toNat state.data

end CPythonListsort

namespace CPythonListsort

/--
[pendingOccurrenceKeys_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma pendingOccurrenceKeys_mirror
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  pendingOccurrenceKeys (mirrorMergeState size state) = (pendingOccurrenceKeys state).map (mirrorOccurrence size) := by
-- proof
  unfold pendingOccurrenceKeys
  rw [mirrorMergeState_pending, List.map_flatMap]
  apply List.flatMap_congr
  intro run _
  simp only [pendingRunOccurrenceKeys_mirror, Array.toList_map]

end CPythonListsort

namespace CPythonListsort

/--
[sorted_mirror_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma sorted_mirror_iff
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {size : Nat}
  {entries : Array (Occurrence alpha)} :
-- imply
  Sorted (occurrenceComparator lt) (entries.map (mirrorOccurrence size)) ↔ Sorted (occurrenceComparator lt) entries := by
-- proof
  simp only [Sorted, Array.toList_map]
  constructor
  · intro h
    have hmapped := List.pairwise_map.mp h
    simpa [Function.comp_def, occurrenceComparator] using hmapped
  · intro h
    apply List.pairwise_map.mpr
    simpa [Function.comp_def, occurrenceComparator] using h

end CPythonListsort

namespace CPythonListsort

/--
[PendingRunsCorrect.toCanonicalMirrored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma PendingRunsCorrect.toCanonicalMirrored
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : Array alpha}
  {size scanned : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (h : PendingRunsCorrect lt input state scanned) :
-- imply
  CanonicalMirroredPendingRunsCorrect lt input size (mirrorMergeState size state) scanned := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · simpa [PendingLayout, mirrorMergeState] using h.layout
  · intro run hrun
    rw [pendingRunOccurrenceKeys_mirror]
    exact (sorted_mirror_iff lt size _).2
      (h.runSorted run (by simpa using hrun))
  · rw [pendingOccurrenceKeys_mirror, List.map_map]
    simpa [Function.comp_def] using h.stableOccurrencePermutation

end CPythonListsort

namespace CPythonListsort

/--
[CanonicalMirroredPendingRunsCorrect.unmirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma CanonicalMirroredPendingRunsCorrect.unmirror
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {input : Array alpha}
  {size scanned : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (h : CanonicalMirroredPendingRunsCorrect lt input size state scanned) :
-- imply
  PendingRunsCorrect lt input (mirrorMergeState size state) scanned := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · simpa [PendingLayout, mirrorMergeState] using h.layout
  · intro run hrun
    rw [pendingRunOccurrenceKeys_mirror]
    exact (sorted_mirror_iff lt size _).2
      (h.runSorted run (by simpa using hrun))
  · rw [pendingOccurrenceKeys_mirror]
    simpa using h.stableAfterUnmirror

end CPythonListsort

namespace CPythonListsort

/--
[EntrySnapshotPermutation.toCanonicalMirrored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma EntrySnapshotPermutation.toCanonicalMirrored
  {alpha : Type u}
  {nu : Type v}
  {source : SortSlice alpha nu}
  {size : Nat}
  {current : SortSlice (Occurrence alpha) nu}
-- given
  (h : EntrySnapshotPermutation source current) :
-- imply
  CanonicalMirroredEntrySnapshotPermutation source size (mirrorSortSlice size current) := by
-- proof
  simpa [CanonicalMirroredEntrySnapshotPermutation, EntrySnapshotPermutation,
    mirrorSortSlice, Array.map_map, Function.comp_def] using h

end CPythonListsort

namespace CPythonListsort

/--
[CanonicalMirroredEntrySnapshotPermutation.unmirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma CanonicalMirroredEntrySnapshotPermutation.unmirror
  {alpha : Type u}
  {nu : Type v}
  {source : SortSlice alpha nu}
  {size : Nat}
  {current : SortSlice (Occurrence alpha) nu}
-- given
  (h : CanonicalMirroredEntrySnapshotPermutation source size current) :
-- imply
  EntrySnapshotPermutation source (mirrorSortSlice size current) := by
-- proof
  simpa [CanonicalMirroredEntrySnapshotPermutation, EntrySnapshotPermutation,
    mirrorSortSlice, Array.map_map, Function.comp_def] using h

end CPythonListsort

namespace CPythonListsort

/--
[ScanRemainderEntriesMatch.toCanonicalMirrored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma ScanRemainderEntriesMatch.toCanonicalMirrored
  {alpha : Type u}
  {nu : Type v}
  {source : SortSlice alpha nu}
  {size scanned : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (h : ScanRemainderEntriesMatch source state scanned) :
-- imply
  CanonicalMirroredScanRemainderEntriesMatch source size (mirrorMergeState size state) scanned := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.scanned_le
  · simpa using h.state_stop_le
  · simpa using h.source_stop_le
  · simp only [mirrorMergeState_data, mirrorMergeState_basekeys,
    mirrorMergeState_listlen]
    rw [sortSliceRangeEntries_mirror, Array.map_map]
    simpa [Function.comp_def] using h.entries_eq

end CPythonListsort

namespace CPythonListsort

/--
[CanonicalMirroredScanRemainderEntriesMatch.unmirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma CanonicalMirroredScanRemainderEntriesMatch.unmirror
  {alpha : Type u}
  {nu : Type v}
  {source : SortSlice alpha nu}
  {size scanned : Nat}
  {state : MergeState (Occurrence alpha) nu}
-- given
  (h : CanonicalMirroredScanRemainderEntriesMatch source size state scanned) :
-- imply
  ScanRemainderEntriesMatch source (mirrorMergeState size state) scanned := by
-- proof
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h.scanned_le
  · simpa using h.state_stop_le
  · simpa using h.source_stop_le
  · simp only [mirrorMergeState_data, mirrorMergeState_basekeys,
    mirrorMergeState_listlen]
    rw [sortSliceRangeEntries_mirror]
    simpa using h.entries_eq

end CPythonListsort

namespace CPythonListsort

/--
[mirrorOccurrence_nonidentity_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
lemma mirrorOccurrence_nonidentity_regression
  {alpha : Type u}
  {nu : Type v} :
-- imply
  mirrorOccurrence 4 originRelabelRegressionOccurrence = ({ value := 17, origin := 3 } : Occurrence Nat) ∧ mirrorOccurrence 4 (mirrorOccurrence 4 originRelabelRegressionOccurrence) = originRelabelRegressionOccurrence := by
-- proof
  decide

end CPythonListsort

/--
[mirrorCountRunResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorCountRunResult_slice_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorCountRunResult size result).slice = mirrorSortSlice size result.slice := by
-- proof
  apply CPythonListsort.mirrorCountRunResult_slice size result

/--
[mirrorCountRunResult_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorCountRunResult_length_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorCountRunResult size result).length = result.length := by
-- proof
  apply CPythonListsort.mirrorCountRunResult_length size result

/--
[mirrorCountRunResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorCountRunResult_fuel_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (mirrorCountRunResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorCountRunResult_fuel size result

/--
[mirrorReverseEqualResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorReverseEqualResult_slice_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ReverseEqualResult (Occurrence alpha) nu} :
-- imply
  (mirrorReverseEqualResult size result).slice = mirrorSortSlice size result.slice := by
-- proof
  apply CPythonListsort.mirrorReverseEqualResult_slice size result

/--
[mirrorReverseEqualResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorReverseEqualResult_fuel_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : ReverseEqualResult (Occurrence alpha) nu} :
-- imply
  (mirrorReverseEqualResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorReverseEqualResult_fuel size result

/--
[mirrorDescendingScanResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorDescendingScanResult_slice_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (mirrorDescendingScanResult size result).slice = mirrorSortSlice size result.slice := by
-- proof
  apply CPythonListsort.mirrorDescendingScanResult_slice size result

/--
[mirrorDescendingScanResult_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorDescendingScanResult_length_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (mirrorDescendingScanResult size result).length = result.length := by
-- proof
  apply CPythonListsort.mirrorDescendingScanResult_length size result

/--
[mirrorDescendingScanResult_equalTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorDescendingScanResult_equalTail_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (mirrorDescendingScanResult size result).equalTail = result.equalTail := by
-- proof
  apply CPythonListsort.mirrorDescendingScanResult_equalTail size result

/--
[mirrorDescendingScanResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorDescendingScanResult_fuel_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (mirrorDescendingScanResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorDescendingScanResult_fuel size result

/--
[mirrorBinarysortResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorBinarysortResult_slice_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : BinarysortResult (Occurrence alpha) nu} :
-- imply
  (mirrorBinarysortResult size result).slice = mirrorSortSlice size result.slice := by
-- proof
  apply CPythonListsort.mirrorBinarysortResult_slice size result

/--
[mirrorBinarysortResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelEquivariance.lean)
-/
@[path]
private lemma mirrorBinarysortResult_fuel_eq
  {alpha : Type u}
  {nu : Type v}
  {size : Nat}
  {result : BinarysortResult (Occurrence alpha) nu} :
-- imply
  (mirrorBinarysortResult size result).fuelExhausted = result.fuelExhausted := by
-- proof
  apply CPythonListsort.mirrorBinarysortResult_fuel size result


-- created on 2026-10-23
