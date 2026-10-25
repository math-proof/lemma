/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/OccurrenceErasureMerges.lean -/

import Def.CPythonListsort.Code.Correctness.OccurrenceErasure
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

end CPythonListsort
