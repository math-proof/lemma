/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
import Def.CPythonListsort.Code.Correctness.OriginRelabelMerges.Part3
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

@[simp] theorem mirrorMergeHiCursor_state (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).state =
      mirrorMergeState size cursor.state := rfl

@[simp] theorem mirrorMergeHiCursor_dest (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).dest = cursor.dest := rfl

@[simp] theorem mirrorMergeHiCursor_ssa (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).ssa = cursor.ssa := rfl

@[simp] theorem mirrorMergeHiCursor_ssb (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).ssb = cursor.ssb := rfl

@[simp] theorem mirrorMergeHiCursor_basea (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).basea = cursor.basea := rfl

@[simp] theorem mirrorMergeHiCursor_na (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).na = cursor.na := rfl

@[simp] theorem mirrorMergeHiCursor_nb (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).nb = cursor.nb := rfl

@[simp] theorem mirrorMergeHiCursor_minGallop (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).minGallop = cursor.minGallop := rfl

@[simp] theorem mirrorMergeHiCursor_phase (size : Nat)
    (cursor : MergeHiCursor (Occurrence alpha) nu) :
    (mirrorMergeHiCursor size cursor).phase = cursor.phase := rfl

end CPythonListsort
