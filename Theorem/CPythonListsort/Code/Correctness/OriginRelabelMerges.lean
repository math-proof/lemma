/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OriginRelabelEquivariance.Part6
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

@[simp] theorem mirrorTempStorage_cells (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).cells =
      storage.cells.map (Option.map (mirrorSortSliceEntry size)) := rfl

@[simp] theorem mirrorTempStorage_backing (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).backing = storage.backing := rfl

@[simp] theorem mirrorTempStorage_hasValues (size : Nat)
    (storage : TempStorage (Occurrence alpha) nu) :
    (mirrorTempStorage size storage).hasValues = storage.hasValues := rfl

@[simp] theorem mirrorMergeState_minGallop (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).min_gallop = state.min_gallop := rfl

@[simp] theorem mirrorMergeState_tempStorage (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).a = mirrorTempStorage size state.a := rfl

@[simp] theorem mirrorMergeState_mrCurrent (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_current = state.mr_current := rfl

@[simp] theorem mirrorMergeState_mrE (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_e = state.mr_e := rfl

@[simp] theorem mirrorMergeState_mrMask (size : Nat)
    (state : MergeState (Occurrence alpha) nu) :
    (mirrorMergeState size state).mr_mask = state.mr_mask := rfl

end CPythonListsort
