/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/MergeHiInvariant.lean -/

import Def.CPythonListsort.Code.Assembly.GallopCorrectness
import Theorem.CPythonListsort.Code.Assembly.MergeHiSafety.Part5
import Def.CPythonListsort.Code.Correctness.MergeMovementCorrectness.Part2
import Structure.CPythonListsort.Code.Correctness.MergeSemanticPre
import Def.CPythonListsort.Code.Correctness.SortSliceRange
import Def.CPythonListsort.Code.Correctness.StableMerge
import Structure.CPythonListsort.Code.Correctness.MergeHiInvariant
/-!
# Semantic invariant for `merge_hi`

The safety invariant for `merge_hi` deliberately records only cursor geometry,
storage validity, and stable state fields.  Functional correctness needs a
separate immutable snapshot of the two post-trimming runs and a description of
the suffix already filled by the right-to-left loop.  This module introduces
that semantic vocabulary without changing the reviewed safety certificate.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-! ## Terminal semantic effects -/

/-- If the sole right entry is strictly below every remaining left entry,
left-biased stable merge emits it first and then the untouched left list. -/
theorem stableEntryMerge_singleton_right_of_all_lt
    (lt : BoolComparator alpha)
    (right : SortSliceEntry (Occurrence alpha) nu) :
    ∀ left : List (SortSliceEntry (Occurrence alpha) nu),
      (∀ leftEntry ∈ left,
        lt right.key.value leftEntry.key.value = true) →
      stableEntryMerge lt left [right] = right :: left
  | [], _ => by simp [stableEntryMerge]
  | leftHead :: leftTail, hstrict => by
      unfold stableEntryMerge
      rw [List.cons_merge_cons]
      have hnot : ¬stableEntryLE lt leftHead right = true := by
        simp [stableEntryLE, stableOccurrenceLE,
          hstrict leftHead (by simp)]
      rw [if_neg hnot]
      simp

end CPythonListsort
