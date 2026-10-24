import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Correctness.OccurrenceErasure
open CPythonListsort


namespace CPythonListsort

/--
[eraseOccurrenceComparator_occurrenceComparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceComparator_occurrenceComparator
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha} :
-- imply
  eraseOccurrenceComparator (occurrenceComparator lt) = lt := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceEntry_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceEntry_key
  {alpha : Type u}
  {nu : Type v}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceEntry entry).key = entry.key.value :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceEntry_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceEntry_value
  {alpha : Type u}
  {nu : Type v}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceEntry entry).value = entry.value :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_entries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_entries
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceSlice slice).entries = slice.entries.map eraseOccurrenceEntry :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_entries_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_entries_size
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceSlice slice).entries.size = slice.entries.size := by
-- proof
  simp [eraseOccurrenceSlice]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceTempStorage_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceTempStorage_cells
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceTempStorage storage).cells = storage.cells.map (Option.map eraseOccurrenceEntry) :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceTempStorage_cells_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceTempStorage_cells_size
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceTempStorage storage).cells.size = storage.cells.size := by
-- proof
  simp [eraseOccurrenceTempStorage]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_data
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).data = eraseOccurrenceSlice state.data :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_tempStorage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_tempStorage
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).a = eraseOccurrenceTempStorage state.a :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_key_compare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_key_compare
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).key_compare = eraseOccurrenceComparator state.key_compare :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_pending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_pending
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).pending = state.pending :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_listlen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_listlen
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).listlen = state.listlen :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_basekeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_basekeys
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).basekeys = state.basekeys :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_alloced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_alloced
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).alloced = state.alloced :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_minrunState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_minrunState
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).minrunState = state.minrunState :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_minGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_minGallop
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).min_gallop = state.min_gallop :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_mrCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_mrCurrent
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).mr_current = state.mr_current :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_mrE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_mrE
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).mr_e = state.mr_e :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_mrMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_mrMask
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeState state).mr_mask = state.mr_mask :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSortImplResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceListSortImplResult_state
  {alpha : Type u}
  {nu : Type v}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceListSortImplResult result).state = eraseOccurrenceMergeState result.state :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSortImplResult_returnCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceListSortImplResult_returnCode
  {alpha : Type u}
  {nu : Type v}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceListSortImplResult result).returnCode = result.returnCode :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceListSortImplResult_fuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceListSortImplResult_fuelExhausted
  {alpha : Type u}
  {nu : Type v}
  {result : ListSortImplResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceListSortImplResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_tagSortSliceOccurrences](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_tagSortSliceOccurrences
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice alpha nu} :
-- imply
  eraseOccurrenceSlice (tagSortSliceOccurrences slice) = slice := by
-- proof
  cases slice with
  | mk entries =>
    simp only [eraseOccurrenceSlice, tagSortSliceOccurrences]
    congr 1
    apply Array.ext <;>
      simp [eraseOccurrenceEntry]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceInput_withOccurrenceKeys](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceInput_withOccurrenceKeys
  {alpha : Type u}
  {nu : Type v}
  {input : ListSortInput alpha nu} :
-- imply
  eraseOccurrenceSlice input.withOccurrenceKeys.slice = input.slice :=
-- proof
eraseOccurrenceSlice_tagSortSliceOccurrences input.slice

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_read](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_read
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {index : Int} :
-- imply
  (eraseOccurrenceSlice slice).read? index = (slice.read? index).map eraseOccurrenceEntry := by
-- proof
  by_cases hindex : 0 ≤ index <;>
    simp [eraseOccurrenceSlice, SortSlice.read?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_write](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_write
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {index : Int}
  {entry : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceSlice slice).write? index (eraseOccurrenceEntry entry) = (slice.write? index entry).map eraseOccurrenceSlice := by
-- proof
  by_cases hindex : 0 ≤ index
  · by_cases hin : index.toNat < slice.entries.size
    · simp [eraseOccurrenceSlice, eraseOccurrenceEntry, SortSlice.write?,
      hindex, hin]
    · simp [eraseOccurrenceSlice, SortSlice.write?, hindex, hin]
  · simp [SortSlice.write?, hindex]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copyFrom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copyFrom
  {alpha : Type u}
  {nu : Type v}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice destination).copyFrom? (eraseOccurrenceSlice source) dst src = (destination.copyFrom? source dst src).map eraseOccurrenceSlice := by
-- proof
  unfold SortSlice.copyFrom?
  rw [eraseOccurrenceSlice_read]
  cases hread : source.read? src with
  | none => simp
  | some entry =>
    simp only [Option.map_some]
    exact eraseOccurrenceSlice_write destination dst entry

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copy
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice slice).copy? dst src = (slice.copy? dst src).map eraseOccurrenceSlice := by
-- proof
  simp [SortSlice.copy?, eraseOccurrenceSlice_copyFrom]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copyFromIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copyFromIncr
  {alpha : Type u}
  {nu : Type v}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice destination).copyFromIncr? (eraseOccurrenceSlice source) dst src = (destination.copyFromIncr? source dst src).map eraseOccurrenceCursorResult := by
-- proof
  unfold SortSlice.copyFromIncr?
  rw [eraseOccurrenceSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [eraseOccurrenceCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copyFromDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copyFromDecr
  {alpha : Type u}
  {nu : Type v}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice destination).copyFromDecr? (eraseOccurrenceSlice source) dst src = (destination.copyFromDecr? source dst src).map eraseOccurrenceCursorResult := by
-- proof
  unfold SortSlice.copyFromDecr?
  rw [eraseOccurrenceSlice_copyFrom]
  cases hcopy : destination.copyFrom? source dst src with
  | none => simp
  | some updated => simp [eraseOccurrenceCursorResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copyIncr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copyIncr
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice slice).copyIncr? dst src = (slice.copyIncr? dst src).map eraseOccurrenceCursorResult := by
-- proof
  simp [SortSlice.copyIncr?, eraseOccurrenceSlice_copyFromIncr]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_copyDecr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_copyDecr
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  (eraseOccurrenceSlice slice).copyDecr? dst src = (slice.copyDecr? dst src).map eraseOccurrenceCursorResult := by
-- proof
  simp [SortSlice.copyDecr?, eraseOccurrenceSlice_copyFromDecr]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_memcpyCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_memcpyCore
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {destination source : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memcpyCore? count (eraseOccurrenceSlice destination) (eraseOccurrenceSlice source) dst src = (SortSlice.memcpyCore? count destination source dst src).map eraseOccurrenceSlice := by
-- proof
  induction count generalizing destination dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memcpyCore?]
    rw [eraseOccurrenceSlice_copyFrom]
    cases hcopy : destination.copyFrom? source dst src with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_memmoveForward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_memmoveForward
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memmoveForward? count (eraseOccurrenceSlice slice) dst src = (SortSlice.memmoveForward? count slice dst src).map eraseOccurrenceSlice := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memmoveForward?]
    rw [eraseOccurrenceSlice_copy]
    cases hcopy : slice.copy? dst src with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_memmoveBackward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_memmoveBackward
  {alpha : Type u}
  {nu : Type v}
  {count : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int} :
-- imply
  SortSlice.memmoveBackward? count (eraseOccurrenceSlice slice) dst src = (SortSlice.memmoveBackward? count slice dst src).map eraseOccurrenceSlice := by
-- proof
  induction count generalizing slice dst src with
  | zero => rfl
  | succ count ih =>
    simp only [SortSlice.memmoveBackward?]
    rw [eraseOccurrenceSlice_copy]
    cases hcopy : slice.copy? (dst + Int.ofNat count)
      (src + Int.ofNat count) with
    | none => simp
    | some updated => simp [ih]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSlice_memmove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSlice_memmove
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {dst src : Int}
  {count : Nat} :
-- imply
  (eraseOccurrenceSlice slice).memmove? dst src count = (slice.memmove? dst src count).map eraseOccurrenceSlice := by
-- proof
  simp only [SortSlice.memmove?]
  cases SortSlice.memmoveDirection dst src <;>
    simp [eraseOccurrenceSlice_memmoveForward,
      eraseOccurrenceSlice_memmoveBackward]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrencePushPendingRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrencePushPendingRun
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {run : PendingRun} :
-- imply
  pushPendingRun (eraseOccurrenceMergeState state) run = eraseOccurrenceMergeState (pushPendingRun state run) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceInstallMinrunState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceInstallMinrunState
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {minrun : MinrunState} :
-- imply
  installMinrunState (eraseOccurrenceMergeState state) minrun = eraseOccurrenceMergeState (installMinrunState state minrun) := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_setData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_setData
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {data : SortSlice (Occurrence alpha) nu} :
-- imply
  { eraseOccurrenceMergeState state with data := eraseOccurrenceSlice data } = eraseOccurrenceMergeState { state with data := data } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeState_setPending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeState_setPending
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {pending : Array PendingRun} :
-- imply
  { eraseOccurrenceMergeState state with pending := pending } = eraseOccurrenceMergeState { state with pending := pending } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[expandedEraseOccurrenceMergeStateWithMinGallop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma expandedEraseOccurrenceMergeStateWithMinGallop
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {minGallop : PySSize} :
-- imply
  ({ min_gallop := minGallop listlen := (eraseOccurrenceMergeState state).listlen basekeys := (eraseOccurrenceMergeState state).basekeys data := eraseOccurrenceSlice state.data a := eraseOccurrenceTempStorage state.a alloced := (eraseOccurrenceMergeState state).alloced pending := (eraseOccurrenceMergeState state).pending key_compare := (eraseOccurrenceMergeState state).key_compare mr_current := (eraseOccurrenceMergeState state).mr_current mr_e := (eraseOccurrenceMergeState state).mr_e mr_mask := (eraseOccurrenceMergeState state).mr_mask } : MergeState alpha nu) = eraseOccurrenceMergeState { state with min_gallop := minGallop } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[iflt_eraseOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma iflt_eraseOccurrence
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : Occurrence alpha} :
-- imply
  iflt lt left.value right.value = iflt (occurrenceComparator lt) left right := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeGetmemResult_state](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeGetmemResult_state
  {alpha : Type u}
  {nu : Type v}
  {result : MergeGetmemResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeGetmemResult result).state = eraseOccurrenceMergeState result.state :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeGetmemResult_outcome](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeGetmemResult_outcome
  {alpha : Type u}
  {nu : Type v}
  {result : MergeGetmemResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceMergeGetmemResult result).outcome = result.outcome :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeFreemem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeFreemem
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu} :
-- imply
  mergeFreemem (eraseOccurrenceMergeState state) = eraseOccurrenceMergeState (mergeFreemem state) := by
-- proof
  by_cases hinline : state.a.backing = .inline <;>
    simp [mergeFreemem, hinline, eraseOccurrenceMergeState,
      eraseOccurrenceTempStorage]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeGetmemAllocationLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeGetmemAllocationLimit
  {alpha : Type u}
  {nu : Type v}
  {storage : TempStorage (Occurrence alpha) nu} :
-- imply
  mergeGetmemAllocationLimit (eraseOccurrenceTempStorage storage) = mergeGetmemAllocationLimit storage := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceMergeGetmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceMergeGetmem
  {alpha : Type u}
  {nu : Type v}
  {state : MergeState (Occurrence alpha) nu}
  {need : PySSize} :
-- imply
  mergeGetmem (eraseOccurrenceMergeState state) need = eraseOccurrenceMergeGetmemResult (mergeGetmem state need) := by
-- proof
  have hlimit :
    mergeGetmemAllocationLimit (eraseOccurrenceMergeState state).a =
      mergeGetmemAllocationLimit state.a := by rfl
  rw [mergeGetmem, mergeGetmem]
  rw [eraseOccurrenceMergeState_alloced, hlimit]
  by_cases hreuse : need.sle state.alloced = true
  · simp [hreuse, eraseOccurrenceMergeGetmemResult]
  · have hreuseFalse : need.sle state.alloced = false := by
    cases h : need.sle state.alloced <;> simp_all
    by_cases hguard : mergeGetmemAllocationLimit state.a < need.toNat
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard, if_true,
      eraseOccurrenceMergeGetmemResult]
      rw [eraseOccurrenceMergeFreemem]
    · simp only [hreuseFalse, Bool.false_eq_true, if_false, hguard]
      rw [eraseOccurrenceMergeFreemem]
      simp [eraseOccurrenceMergeGetmemResult, eraseOccurrenceMergeState,
        eraseOccurrenceTempStorage]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopLeftRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopLeftRightExponential
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopLeftRightExponential? fuel lt (eraseOccurrenceSlice slice) base key.value hint maxOffset lastOffset offset = gallopLeftRightExponential? fuel (occurrenceComparator lt) slice base key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftRightExponential?]
    by_cases hactive : offset < maxOffset
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopLeftLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopLeftLeftExponential
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopLeftLeftExponential? fuel lt (eraseOccurrenceSlice slice) base key.value hint maxOffset lastOffset offset = gallopLeftLeftExponential? fuel (occurrenceComparator lt) slice base key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftLeftExponential?]
    by_cases hactive : offset < maxOffset
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopLeftBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopLeftBinary
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
  {lower upper : Nat} :
-- imply
  gallopLeftBinary? fuel lt (eraseOccurrenceSlice slice) base key.value lower upper = gallopLeftBinary? fuel (occurrenceComparator lt) slice base key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopLeftBinary?]
    by_cases hactive : lower < upper
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read?
        (base + Int.ofNat (lower + (upper - lower) / 2)) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFinishGallopLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceFinishGallopLeft
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exponentialFuelExhausted : Bool} :
-- imply
  finishGallopLeft? fuel lt (eraseOccurrenceSlice slice) base key.value n lastOffset upperOffset exponentialFuelExhausted = finishGallopLeft? fuel (occurrenceComparator lt) slice base key n lastOffset upperOffset exponentialFuelExhausted := by
-- proof
  unfold finishGallopLeft?
  by_cases hbounds :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n
  · rw [if_pos hbounds, if_pos hbounds]
    by_cases hnonnegative : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · rw [if_pos hnonnegative, if_pos hnonnegative]
      by_cases hexhausted : exponentialFuelExhausted = true
      · simp [hexhausted]
      · simp [hexhausted, eraseOccurrenceGallopLeftBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopRightLeftExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopRightLeftExponential
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopRightLeftExponential? fuel lt (eraseOccurrenceSlice slice) base key.value hint maxOffset lastOffset offset = gallopRightLeftExponential? fuel (occurrenceComparator lt) slice base key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightLeftExponential?]
    by_cases hactive : offset < maxOffset
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read? (base + Int.ofNat hint - Int.ofNat offset) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopRightRightExponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopRightRightExponential
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (hint maxOffset lastOffset offset : Nat) :
-- imply
  gallopRightRightExponential? fuel lt (eraseOccurrenceSlice slice) base key.value hint maxOffset lastOffset offset = gallopRightRightExponential? fuel (occurrenceComparator lt) slice base key hint maxOffset lastOffset offset := by
-- proof
  induction fuel generalizing lastOffset offset with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightRightExponential?]
    by_cases hactive : offset < maxOffset
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read? (base + Int.ofNat hint + Int.ofNat offset) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopRightBinary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopRightBinary
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
  {lower upper : Nat} :
-- imply
  gallopRightBinary? fuel lt (eraseOccurrenceSlice slice) base key.value lower upper = gallopRightBinary? fuel (occurrenceComparator lt) slice base key lower upper := by
-- proof
  induction fuel generalizing lower upper with
  | zero => rfl
  | succ fuel ih =>
    simp only [gallopRightBinary?]
    by_cases hactive : lower < upper
    · rw [if_pos hactive, if_pos hactive, eraseOccurrenceSlice_read]
      cases hread : slice.read?
        (base + Int.ofNat (lower + (upper - lower) / 2)) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, gallopBindOptionAcross]
        simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
        split <;> simp [ih]
    · simp [hactive]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFinishGallopRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceFinishGallopRight
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
  {n : Nat}
  {lastOffset upperOffset : Int}
  {exponentialFuelExhausted : Bool} :
-- imply
  finishGallopRight? fuel lt (eraseOccurrenceSlice slice) base key.value n lastOffset upperOffset exponentialFuelExhausted = finishGallopRight? fuel (occurrenceComparator lt) slice base key n lastOffset upperOffset exponentialFuelExhausted := by
-- proof
  unfold finishGallopRight?
  by_cases hbounds :
    -1 ≤ lastOffset ∧ lastOffset < upperOffset ∧ upperOffset ≤ Int.ofNat n
  · rw [if_pos hbounds, if_pos hbounds]
    by_cases hnonnegative : 0 ≤ lastOffset + 1 ∧ 0 ≤ upperOffset
    · rw [if_pos hnonnegative, if_pos hnonnegative]
      by_cases hexhausted : exponentialFuelExhausted = true
      · simp [hexhausted]
      · simp [hexhausted, eraseOccurrenceGallopRightBinary]
    · rw [if_neg hnonnegative, if_neg hnonnegative]
  · rw [if_neg hbounds, if_neg hbounds]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopLeft
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (n hint : Nat)
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  gallopLeft? (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base key.value n hint = gallopLeft? state slice base key n hint := by
-- proof
  unfold gallopLeft?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  split <;> try rfl
  rw [eraseOccurrenceSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, gallopBindOptionAcross]
    simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
    split
    · rw [eraseOccurrenceGallopLeftRightExponential]
      cases hexponential : gallopLeftRightExponential? (n + 1)
        (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
      | none => rfl
      | some exponential =>
        simp [eraseOccurrenceFinishGallopLeft]
    · rw [eraseOccurrenceGallopLeftLeftExponential]
      cases hexponential : gallopLeftLeftExponential? (n + 1)
        (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
      | none => rfl
      | some exponential =>
        simp [eraseOccurrenceFinishGallopLeft]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceGallopRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceGallopRight
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {key : Occurrence alpha}
-- given
  (n hint : Nat)
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  gallopRight? (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base key.value n hint = gallopRight? state slice base key n hint := by
-- proof
  unfold gallopRight?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  split <;> try rfl
  rw [eraseOccurrenceSlice_read]
  cases hread : slice.read? (base + Int.ofNat hint) with
  | none => rfl
  | some entry =>
    simp only [Option.map_some, gallopBindOptionAcross]
    simp only [eraseOccurrenceEntry_key, iflt_eraseOccurrence]
    split
    · rw [eraseOccurrenceGallopRightLeftExponential]
      cases hexponential : gallopRightLeftExponential? (n + 1)
        (occurrenceComparator lt) slice base key hint (hint + 1) 0 1 with
      | none => rfl
      | some exponential =>
        simp [eraseOccurrenceFinishGallopRight]
    · rw [eraseOccurrenceGallopRightRightExponential]
      cases hexponential : gallopRightRightExponential? (n + 1)
        (occurrenceComparator lt) slice base key hint (n - hint) 0 1 with
      | none => rfl
      | some exponential =>
        simp [eraseOccurrenceFinishGallopRight]
/-! ## Front-end evaluator erasure -/

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceReverseSliceLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceReverseSliceLoop
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
-- given
  (lo hi : Int) :
-- imply
  reverseSliceLoop? fuel (eraseOccurrenceSlice slice) lo hi = (reverseSliceLoop? fuel slice lo hi).map eraseOccurrenceReverseSliceResult := by
-- proof
  induction fuel generalizing slice lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [reverseSliceLoop?]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      rw [eraseOccurrenceSlice_read]
      cases hleft : slice.read? lo with
      | none => simp
      | some left =>
        simp only [Option.map_some]
        rw [eraseOccurrenceSlice_read]
        cases hright : slice.read? hi with
        | none => simp
        | some right =>
          cases hwriteLeft : slice.write? lo right with
          | none => simp [hwriteLeft, eraseOccurrenceSlice_write]
          | some afterLeft =>
            cases hwriteRight : afterLeft.write? hi left with
            | none =>
              simp [hwriteLeft, hwriteRight,
                eraseOccurrenceSlice_write]
            | some afterRight =>
              simp [hwriteLeft, hwriteRight,
                eraseOccurrenceSlice_write, ih]
    · simp [hactive, eraseOccurrenceReverseSliceResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceReverseSlice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceReverseSlice
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
-- given
  (lo hi : Int) :
-- imply
  reverseSlice? (eraseOccurrenceSlice slice) lo hi = (reverseSlice? slice lo hi).map eraseOccurrenceReverseSliceResult := by
-- proof
  unfold reverseSlice?
  by_cases horder : lo ≤ hi
  · rw [if_pos horder, if_pos horder]
    by_cases hactive : lo < hi
    · rw [if_pos hactive, if_pos hactive]
      exact eraseOccurrenceReverseSliceLoop (hi - lo).toNat slice lo (hi - 1)
    · simp [hactive, eraseOccurrenceReverseSliceResult]
  · simp [horder]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceSortsliceReverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceSortsliceReverse
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {count : Nat} :
-- imply
  sortsliceReverse? (eraseOccurrenceSlice slice) base count = (sortsliceReverse? slice base count).map eraseOccurrenceReverseSliceResult := by
-- proof
  simp [sortsliceReverse?, eraseOccurrenceReverseSlice]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceCountRunResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceCountRunResult_slice
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceCountRunResult result).slice = eraseOccurrenceSlice result.slice :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceCountRunResult_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceCountRunResult_length
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceCountRunResult result).length = result.length :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceCountRunResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceCountRunResult_fuel
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : CountRunResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceCountRunResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceReverseEqualResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceReverseEqualResult_slice
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : ReverseEqualResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceReverseEqualResult result).slice = eraseOccurrenceSlice result.slice :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceReverseEqualResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceReverseEqualResult_fuel
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : ReverseEqualResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceReverseEqualResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceDescendingScanResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceDescendingScanResult_slice
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceDescendingScanResult result).slice = eraseOccurrenceSlice result.slice :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceDescendingScanResult_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceDescendingScanResult_length
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceDescendingScanResult result).length = result.length :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceDescendingScanResult_equalTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceDescendingScanResult_equalTail
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceDescendingScanResult result).equalTail = result.equalTail :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceDescendingScanResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceDescendingScanResult_fuel
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : DescendingScanResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceDescendingScanResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[iflt_eraseOccurrenceEntry_occurrenceComparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma iflt_eraseOccurrenceEntry_occurrenceComparator
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {left right : SortSliceEntry (Occurrence alpha) nu} :
-- imply
  iflt lt (eraseOccurrenceEntry left).key (eraseOccurrenceEntry right).key = iflt (occurrenceComparator lt) left.key right.key := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceAscendingScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceAscendingScan
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n : Nat} :
-- imply
  ascendingScan? fuel lt (eraseOccurrenceSlice slice) base nremaining n = ascendingScan? fuel (occurrenceComparator lt) slice base nremaining n := by
-- proof
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [ascendingScan?]
    by_cases hscan : n < nremaining
    · rw [if_pos hscan, if_pos hscan]
      rw [eraseOccurrenceSlice_read]
      cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
      | none => rfl
      | some previous =>
        simp only [Option.map_some, countRunBindOptionAcross]
        rw [eraseOccurrenceSlice_read]
        cases hnext : slice.read? (base + Int.ofNat n) with
        | none => rfl
        | some next =>
          simp only [Option.map_some]
          rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
          split <;> simp [ih]
    · simp [hscan]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceReverseLastEqual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceReverseLastEqual
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n neq : Nat} :
-- imply
  reverseLastEqual? (eraseOccurrenceSlice slice) base n neq = (reverseLastEqual? slice base n neq).map eraseOccurrenceReverseEqualResult := by
-- proof
  unfold reverseLastEqual?
  by_cases heq : neq = 0
  · simp [heq, eraseOccurrenceReverseEqualResult]
  · rw [if_neg heq, if_neg heq]
    dsimp only
    rw [eraseOccurrenceSortsliceReverse]
    cases hreversed : sortsliceReverse? slice
      (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) with
    | none => simp
    | some reversed =>
      simp [eraseOccurrenceReverseEqualResult,
        eraseOccurrenceReverseSliceResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceDescendingScan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceDescendingScan
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n neq : Nat} :
-- imply
  descendingScan? fuel lt (eraseOccurrenceSlice slice) base nremaining n neq = (descendingScan? fuel (occurrenceComparator lt) slice base nremaining n neq).map eraseOccurrenceDescendingScanResult := by
-- proof
  induction fuel generalizing slice n neq with
  | zero => rfl
  | succ fuel ih =>
    simp only [descendingScan?]
    by_cases hscan : n < nremaining
    · rw [if_pos hscan, if_pos hscan]
      rw [eraseOccurrenceSlice_read]
      cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
      | none => simp
      | some previous =>
        simp only [Option.map_some]
        rw [eraseOccurrenceSlice_read]
        cases hnext : slice.read? (base + Int.ofNat n) with
        | none => simp
        | some next =>
          simp only [Option.map_some, Option.bind_eq_bind,
            Option.bind_some]
          rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
          by_cases hless :
            iflt (occurrenceComparator lt) next.key previous.key = true
          · simp only [iflt_eq] at hless
            simp only [iflt_eq]
            rw [eraseOccurrenceReverseLastEqual]
            cases hreversed : reverseLastEqual? slice base n neq with
            | none => simp [hless]
            | some reversed =>
              cases hfuel : reversed.fuelExhausted <;>
                simp [hless, hfuel,
                  eraseOccurrenceReverseEqualResult,
                  eraseOccurrenceDescendingScanResult, ih]
          · rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
            by_cases hgreater :
              iflt (occurrenceComparator lt) previous.key next.key = true
            · simp only [iflt_eq] at hless hgreater
              simp [iflt_eq, hless, hgreater,
                eraseOccurrenceDescendingScanResult]
            · simp only [iflt_eq] at hless hgreater
              simp [iflt_eq, hless, hgreater, ih]
    · simp [hscan, eraseOccurrenceDescendingScanResult]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceFinishDescending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceFinishDescending
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining n : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  finishDescending? (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base nremaining n = (finishDescending? state slice base nremaining n).map eraseOccurrenceCountRunResult := by
-- proof
  unfold finishDescending?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  rw [eraseOccurrenceDescendingScan]
  cases hdescending : descendingScan? nremaining
    (occurrenceComparator lt) slice base nremaining n 0 with
  | none => simp
  | some descending =>
    by_cases hfuel : descending.fuelExhausted = true
    · simp [hfuel, eraseOccurrenceDescendingScanResult,
      eraseOccurrenceCountRunResult]
    · cases hequal : reverseLastEqual? descending.slice base
      descending.length descending.equalTail with
      | none =>
        simp [hfuel, hequal, eraseOccurrenceDescendingScanResult]
      | some equalReversed =>
        by_cases hequalFuel : equalReversed.fuelExhausted = true
        · simp [hfuel, hequal, hequalFuel,
          eraseOccurrenceDescendingScanResult,
          eraseOccurrenceReverseEqualResult,
          eraseOccurrenceCountRunResult]
        · cases hwhole : sortsliceReverse? equalReversed.slice base
          descending.length with
          | none =>
            simp [hfuel, hequal, hequalFuel, hwhole,
              eraseOccurrenceDescendingScanResult,
              eraseOccurrenceReverseEqualResult]
          | some wholeReversed =>
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · simp [hfuel, hequal, hequalFuel, hwhole, hwholeFuel,
              eraseOccurrenceDescendingScanResult,
              eraseOccurrenceReverseEqualResult,
              eraseOccurrenceReverseSliceResult,
              eraseOccurrenceCountRunResult]
            · simp only [hfuel, Bool.false_eq_true, if_false,
              Option.map_some, Option.bind_eq_bind, Option.bind_some,
              eraseOccurrenceDescendingScanResult_fuel,
              eraseOccurrenceDescendingScanResult_slice,
              eraseOccurrenceDescendingScanResult_length,
              eraseOccurrenceDescendingScanResult_equalTail]
              rw [eraseOccurrenceReverseLastEqual]
              simp only [hequal, Option.map_some, Option.bind_some,
                eraseOccurrenceReverseEqualResult_fuel,
                eraseOccurrenceReverseEqualResult_slice, hequalFuel,
                Bool.false_eq_true, if_false]
              rw [eraseOccurrenceSortsliceReverse]
              simp only [hwhole, Option.map_some, Option.bind_some,
                eraseOccurrenceReverseSliceResult, hwholeFuel,
                Bool.false_eq_true, if_false]
              rw [eraseOccurrenceAscendingScan]
              cases hascending : ascendingScan? nremaining
                (occurrenceComparator lt) wholeReversed.slice base
                nremaining descending.length <;> rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceCountRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceCountRun
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {nremaining : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  countRun? (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base nremaining = (countRun? state slice base nremaining).map eraseOccurrenceCountRunResult := by
-- proof
  unfold countRun?
  simp only [eraseOccurrenceMergeState_key_compare, hcompare,
    eraseOccurrenceComparator_occurrenceComparator]
  by_cases hvalid : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hvalid, if_pos hvalid, eraseOccurrenceAscendingScan]
    cases hascending : ascendingScan? nremaining
      (occurrenceComparator lt) slice base nremaining 1 with
    | none => simp [countRunBindOptionAcross]
    | some ascending =>
      cases hfuel : ascending.fuelExhausted with
      | true =>
        simp [countRunBindOptionAcross, hfuel,
          eraseOccurrenceCountRunResult]
      | false =>
        by_cases hcomplete : ascending.length = nremaining
        · simp [countRunBindOptionAcross, hfuel, hcomplete,
          eraseOccurrenceCountRunResult]
        · by_cases hlong : 1 < ascending.length
          · simp only [countRunBindOptionAcross, hfuel,
            Bool.false_eq_true, if_false, hcomplete, hlong, if_true]
            rw [eraseOccurrenceSlice_read]
            cases hfirst : slice.read? base with
            | none => simp
            | some first =>
              simp only [Option.map_some]
              rw [eraseOccurrenceSlice_read]
              cases hlast : slice.read?
                (base + Int.ofNat (ascending.length - 1)) with
              | none => simp
              | some last =>
                simp only [Option.map_some, Option.bind_eq_bind,
                  Option.bind_some]
                rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
                by_cases hordered :
                  occurrenceComparator lt first.key last.key = true
                · simp [hordered, iflt,
                  eraseOccurrenceCountRunResult]
                · cases hreversed : sortsliceReverse? slice base
                  ascending.length with
                  | none => simp [hordered, iflt, hreversed]
                  | some reversed =>
                    cases hreverseFuel : reversed.fuelExhausted with
                    | true =>
                      simp [hordered, iflt, hreversed,
                        hreverseFuel,
                        eraseOccurrenceReverseSliceResult,
                        eraseOccurrenceCountRunResult]
                    | false =>
                      simp [hordered, iflt, hreversed,
                        hreverseFuel,
                        eraseOccurrenceReverseSliceResult,
                        eraseOccurrenceFinishDescending lt state
                          reversed.slice base nremaining
                          (ascending.length + 1) hcompare]
          · simp only [countRunBindOptionAcross, hfuel,
            Bool.false_eq_true, if_false, hcomplete, hlong]
            exact eraseOccurrenceFinishDescending lt state slice base
              nremaining (ascending.length + 1) hcompare
  · simp [hvalid]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceBinarysortResult_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceBinarysortResult_slice
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : BinarysortResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceBinarysortResult result).slice = eraseOccurrenceSlice result.slice :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceBinarysortResult_fuel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceBinarysortResult_fuel
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {result : BinarysortResult (Occurrence alpha) nu} :
-- imply
  (eraseOccurrenceBinarysortResult result).fuelExhausted = result.fuelExhausted :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceBinarysortSearch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceBinarysortSearch
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {pivot : SortSliceEntry (Occurrence alpha) nu}
  {left right : Nat} :
-- imply
  binarysortSearch? fuel lt (eraseOccurrenceSlice slice) base (eraseOccurrenceEntry pivot) left right = binarysortSearch? fuel (occurrenceComparator lt) slice base pivot left right := by
-- proof
  induction fuel generalizing left right with
  | zero => rfl
  | succ fuel ih =>
    simp only [binarysortSearch?]
    by_cases hsearch : left < right
    · rw [if_pos hsearch, if_pos hsearch, eraseOccurrenceSlice_read]
      cases hread : slice.read?
        (base + Int.ofNat ((left + right) / 2)) with
      | none => rfl
      | some entry =>
        simp only [Option.map_some, binarysortBindOptionAcross]
        rw [iflt_eraseOccurrenceEntry_occurrenceComparator]
        split <;> simp [ih]
    · simp [hsearch]

end CPythonListsort

namespace CPythonListsort

/--
[eraseOccurrenceBinarysortLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceBinarysortLoop
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {fuel : Nat}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n ok : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  binarysortLoop? fuel (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base n ok = (binarysortLoop? fuel state slice base n ok).map eraseOccurrenceBinarysortResult := by
-- proof
  induction fuel generalizing slice ok with
  | zero => rfl
  | succ fuel ih =>
    simp only [binarysortLoop?]
    by_cases hloop : ok < n
    · rw [if_pos hloop, if_pos hloop, eraseOccurrenceSlice_read]
      cases hpivot : slice.read? (base + Int.ofNat ok) with
      | none => simp [binarysortBindOptionAcross]
      | some pivot =>
        simp only [Option.map_some, binarysortBindOptionAcross]
        simp only [eraseOccurrenceMergeState_key_compare, hcompare,
          eraseOccurrenceComparator_occurrenceComparator]
        rw [eraseOccurrenceBinarysortSearch]
        cases hsearch : binarysortSearch? (ok + 1)
          (occurrenceComparator lt) slice base pivot 0 ok with
        | none => simp
        | some search =>
          cases hfuel : search.fuelExhausted with
          | true =>
            simp [hfuel, eraseOccurrenceBinarysortResult]
          | false =>
            simp only [hfuel, Bool.false_eq_true, if_false]
            rw [eraseOccurrenceSlice_memmove]
            cases hmove : slice.memmove?
              (base + Int.ofNat (search.position + 1))
              (base + Int.ofNat search.position)
              (ok - search.position) with
            | none => simp
            | some moved =>
              simp only [Option.map_some, Int.ofNat_eq_natCast,
                Option.bind_eq_bind, Option.bind_some,
                eraseOccurrenceSlice_write, Option.map_bind,
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
[eraseOccurrenceBinarysort](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasure.lean)
-/
@[path]
lemma eraseOccurrenceBinarysort
  {alpha : Type u}
  {nu : Type v}
  {alpha : Type u}
  {nu : Type v}
  {lt : BoolComparator alpha}
  {state : MergeState (Occurrence alpha) nu}
  {slice : SortSlice (Occurrence alpha) nu}
  {base : Int}
  {n ok : Nat}
-- given
  (hcompare : state.key_compare = occurrenceComparator lt) :
-- imply
  binarysort? (eraseOccurrenceMergeState state) (eraseOccurrenceSlice slice) base n ok = (binarysort? state slice base n ok).map eraseOccurrenceBinarysortResult := by
-- proof
  unfold binarysort?
  by_cases hvalid : 1 ≤ n ∧ ok ≤ n ∧ n ≤ MAX_MINRUN.toNat
  · rw [if_pos hvalid, if_pos hvalid]
    split <;>
      apply eraseOccurrenceBinarysortLoop lt n state slice base n <;>
      exact hcompare
  · simp [hvalid]

end CPythonListsort


-- created on 2026-10-23
