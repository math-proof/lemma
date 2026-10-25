/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OccurrenceErasure
import Def.CPythonListsort.Code.Correctness.OccurrenceErasureMerges.Part2
/-!
# Occurrence-tag erasure for merge evaluators

The functional-correctness development carries ghost origins in its keys.
This module proves that temporary-storage allocation, galloping, and both
concrete merge engines commute with erasing those origins.
These are evaluator equations only: no ordering or stability law is assumed.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

@[simp] theorem eraseOccurrenceMergeHiCursor_state (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).state =
      eraseOccurrenceMergeState cursor.state := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_dest (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).dest = cursor.dest := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_ssa (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).ssa = cursor.ssa := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_ssb (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).ssb = cursor.ssb := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_basea (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).basea = cursor.basea := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_na (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).na = cursor.na := rfl

@[simp] theorem eraseOccurrenceMergeHiCursor_nb (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (eraseOccurrenceMergeHiCursor cursor).nb = cursor.nb := rfl

end CPythonListsort
