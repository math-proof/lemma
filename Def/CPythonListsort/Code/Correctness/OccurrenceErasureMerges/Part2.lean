/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OccurrenceErasure
import Theorem.CPythonListsort.Code.Correctness.OccurrenceErasureMerges
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

/-- Erase the state carried by one backward-copy cursor result. -/
def eraseOccurrenceMergeHiDataCursorResult
    (result : MergeHiDataCursorResult (Occurrence alpha) nu) :
    MergeHiDataCursorResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    dst := result.dst
    src := result.src }

/-- Erase the state carried by a backward merge result. -/
def eraseOccurrenceMergeHiResult (result : MergeHiResult (Occurrence alpha) nu) :
    MergeHiResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Erase the state carried by a backward merge cursor. -/
def eraseOccurrenceMergeHiCursor (cursor : MergeHiCursor (Occurrence alpha) nu) :
    MergeHiCursor alpha nu :=
  { state := eraseOccurrenceMergeState cursor.state
    dest := cursor.dest
    ssa := cursor.ssa
    ssb := cursor.ssb
    basea := cursor.basea
    na := cursor.na
    nb := cursor.nb
    minGallop := cursor.minGallop
    phase := cursor.phase }

end CPythonListsort
