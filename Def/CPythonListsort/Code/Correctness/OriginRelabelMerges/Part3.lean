/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Theorem.CPythonListsort.Code.Correctness.OriginRelabelMerges.Part3
/-!
# Origin-relabel equivariance for merge evaluators

The reverse-mode transport changes only the recorded origins carried by
occurrence keys.  This module proves that temporary-storage allocation,
galloping, and both concrete merge engines commute with that relabeling.
These are evaluator equations only: no ordering or stability law is assumed.
-/


namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- Relabel the state carried by one backward-copy cursor result. -/
def mirrorMergeHiDataCursorResult (size : Nat)
    (result : MergeHiDataCursorResult (Occurrence alpha) nu) :
    MergeHiDataCursorResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the state carried by a backward merge result. -/
def mirrorMergeHiResult (size : Nat)
    (result : MergeHiResult (Occurrence alpha) nu) :
    MergeHiResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

/-- Relabel the state carried by a backward merge cursor. -/
def mirrorMergeHiCursor (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    MergeHiCursor (Occurrence alpha) nu :=
  { cursor with state := mirrorMergeState size cursor.state }

end CPythonListsort
