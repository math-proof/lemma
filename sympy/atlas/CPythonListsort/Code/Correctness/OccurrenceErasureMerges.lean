/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean -/

import sympy.atlas.CPythonListsort.Code.Correctness.OccurrenceErasure

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

/-- Erase the occurrence-bearing state of a forward merge machine. -/
def eraseOccurrenceMergeLoMachine (machine : MergeLoMachine (Occurrence alpha) nu) :
    MergeLoMachine alpha nu :=
  { state := eraseOccurrenceMergeState machine.state
    dest := machine.dest
    aPos := machine.aPos
    bPos := machine.bPos
    na := machine.na
    nb := machine.nb
    minGallop := machine.minGallop }

/-- Erase the occurrence-bearing state of a forward merge result. -/
def eraseOccurrenceMergeLoResult (result : MergeLoResult (Occurrence alpha) nu) :
    MergeLoResult alpha nu :=
  { state := eraseOccurrenceMergeState result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

@[simp] theorem eraseOccurrenceMergeLoResult_state (result : MergeLoResult (Occurrence alpha) nu) :
    (eraseOccurrenceMergeLoResult result).state =
      eraseOccurrenceMergeState result.state := rfl

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
