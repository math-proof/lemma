/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean -/

import Def.CPythonListsort.Code.Transcription.MergeHi.Part6
import Def.CPythonListsort.Code.Transcription.MergeLo.Part6
import Structure.CPythonListsort.Code.Transcription.MergeAt
/-!
# Pending-stack merge dispatch

This module transcribes CPython's `merge_at`.  The pending-stack replacement
happens before either galloping search, exactly as it does in C, so a later
modeled failure retains that mutation.  The two searches trim entries already
in their final positions and the shorter remaining run selects `merge_lo` or
`merge_hi`.
-/


namespace CPythonListsort

universe u v w x

variable {κ : Type u} {ν : Type v}

def mergeAtSuccess (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

def mergeAtOutOfFuel (state : MergeState κ ν) : MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

def fromMergeLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

def fromMergeHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Replace pending runs `i` and `i+1` by their combined run.  Erasing the
second run also performs CPython's explicit slide when `i` is third-last. -/
def combinePendingAt (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  let combined := { left with len := left.len + right.len }
  let pending := (state.pending.setIfInBounds i combined).eraseIdxIfInBounds (i + 1)
  { state with pending := pending }

end CPythonListsort
