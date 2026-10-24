/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OriginRelabelMerges.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OriginRelabelEquivariance

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

/-! ## Temporary storage and allocation -/

/-- Relabel the state component returned by `mergeGetmem`. -/
def mirrorMergeGetmemResult (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    MergeGetmemResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeGetmemResult_state (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeGetmemResult_outcome (size : Nat)
    (result : MergeGetmemResult (Occurrence alpha) nu) :
    (mirrorMergeGetmemResult size result).outcome = result.outcome := rfl

/-- Relabel the occurrence-bearing state of a forward merge machine. -/
def mirrorMergeLoMachine (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    MergeLoMachine (Occurrence alpha) nu :=
  { machine with state := mirrorMergeState size machine.state }

/-- Relabel the occurrence-bearing state of a forward merge result. -/
def mirrorMergeLoResult (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    MergeLoResult (Occurrence alpha) nu :=
  { result with state := mirrorMergeState size result.state }

@[simp] theorem mirrorMergeLoResult_state (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).state =
      mirrorMergeState size result.state := rfl

@[simp] theorem mirrorMergeLoResult_returnCode (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).returnCode = result.returnCode := rfl

@[simp] theorem mirrorMergeLoResult_fuelExhausted (size : Nat)
    (result : MergeLoResult (Occurrence alpha) nu) :
    (mirrorMergeLoResult size result).fuelExhausted = result.fuelExhausted := rfl

@[simp] theorem mirrorMergeLoMachine_state (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).state =
      mirrorMergeState size machine.state := rfl

@[simp] theorem mirrorMergeLoMachine_dest (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).dest = machine.dest := rfl

@[simp] theorem mirrorMergeLoMachine_aPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).aPos = machine.aPos := rfl

@[simp] theorem mirrorMergeLoMachine_bPos (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).bPos = machine.bPos := rfl

@[simp] theorem mirrorMergeLoMachine_na (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).na = machine.na := rfl

@[simp] theorem mirrorMergeLoMachine_nb (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).nb = machine.nb := rfl

@[simp] theorem mirrorMergeLoMachine_minGallop (size : Nat)
    (machine : MergeLoMachine (Occurrence alpha) nu) :
    (mirrorMergeLoMachine size machine).minGallop = machine.minGallop := rfl

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

private structure MergeComparatorFrame (before after : MergeState κ ν) : Prop
    where
  comparator : after.key_compare = before.key_compare

namespace MergeComparatorFrame
