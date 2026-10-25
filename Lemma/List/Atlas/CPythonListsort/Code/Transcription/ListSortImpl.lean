import Mathlib
import sympy.Basic
import Theorem.CPythonListsort.Code.Transcription.ListSortImpl
open CPythonListsort


namespace CPythonListsort

/--
[initialMergeState_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean)
-/
@[path]
lemma initialMergeState_data
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (hasKeyfunc : Bool) :
-- imply
  (initialMergeState lt hasKeyfunc input).1.data = input := by
-- proof
  simp [initialMergeState]

end CPythonListsort

namespace CPythonListsort

/--
[initialMergeState_temp_hasValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean)
-/
@[path]
lemma initialMergeState_temp_hasValues
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {input : SortSlice κ ν}
-- given
  (hasKeyfunc : Bool) :
-- imply
  (initialMergeState lt hasKeyfunc input).1.a.hasValues = hasKeyfunc := by
-- proof
  simp [initialMergeState, mergeInitTemp]

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_size](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean)
-/
@[path]
lemma pushPendingRun_size
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  (pushPendingRun state run).pending.size = state.pending.size + 1 := by
-- proof
  simp [pushPendingRun]

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRun_at_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/ListSortImpl.lean)
-/
@[path]
lemma pushPendingRun_at_capacity
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {run : PendingRun}
-- given
  (hDepth : state.pending.size = MAX_MERGE_PENDING) :
-- imply
  (pushPendingRun state run).pending.size = MAX_MERGE_PENDING + 1 := by
-- proof
  simp [hDepth]

end CPythonListsort


-- created on 2026-10-23
