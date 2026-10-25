/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
/-!
# `merge_at` safety

This module instruments the pending-stack updates and the two trimming gallops
performed by `merge_at`, then delegates the selected merge continuation to the
already traced `merge_lo` or `merge_hi` evaluator.  The logical shrink of the
active pending array is not an indexed C access; the indexed reads and writes
which precede it are recorded in source order.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Convert a traced `merge_lo` result to the common `merge_at` result. -/
def mergeAtFromLo (result : MergeLoResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Convert a traced `merge_hi` result to the common `merge_at` result. -/
def mergeAtFromHi (result : MergeHiResult κ ν) : MergeAtResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

def mergeAtSuccessResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

def mergeAtOutOfFuelResult (state : MergeState κ ν) :
    MergeAtResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

/-- The logical pending-stack splice performed by `merge_at`.  The traced
implementation below proves that its physical write sequence computes this
state. -/
def mergeAtCombinedState (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : MergeState κ ν :=
  { state with
    pending :=
      (state.pending.setIfInBounds i
        { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) }

/-- Trace the C-level pending writes which install the combined run and, on the
third-last branch, slide the uninvolved last run down one slot.  The returned
state uses the reviewed transcription's single logical splice; the preceding
typed operations establish and record the corresponding physical accesses.
-/
def mergeAtPendingUpdateTraced? (state : MergeState κ ν) (i : Nat)
    (left right : PendingRun) : TraceResult (MergeState κ ν) :=
  let combined : PendingRun := { left with len := left.len + right.len }
  let updated :=
    (TraceResult.pendingRunWrite? state (Int.ofNat i) combined).bind fun written =>
      if i + 3 = state.pending.size then
        (TraceResult.pendingRunRead? written (Int.ofNat (i + 2))).bind fun last =>
          (TraceResult.pendingRunWrite? written (Int.ofNat (i + 1)) last).map
            (fun slid =>
              { slid with pending := slid.pending.eraseIdxIfInBounds (i + 2) })
      else
        TraceResult.pure
          { written with pending := written.pending.eraseIdxIfInBounds (i + 1) }
  updated.recordSuccessPolicyEvent fun _ =>
    .merge
      { index := i
        left := RunSpan.ofPendingRun left
        right := RunSpan.ofPendingRun right }

def mergeAtAfterTrimBTraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB lastA : SortSliceEntry κ ν)
    (trimA trimB : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimB.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if right.len.toNat < trimB.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    let nb := trimB.index
    if nb = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else if na ≤ nb then
      TraceResult.pure (.mergeLo
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })
    else
      TraceResult.pure (.mergeHi
        { state := call
          ssa := Int.ofNat ssa
          ssb := Int.ofNat right.base
          na := na
          nb := nb
          left := left
          right := right
          firstB := firstB
          lastA := lastA
          trimA := trimA
          trimB := trimB })

def mergeAtAfterTrimATraced (call : MergeState κ ν)
    (left right : PendingRun) (firstB : SortSliceEntry κ ν)
    (trimA : GallopResult) : TraceResult (MergeAtPreparation κ ν) :=
  if trimA.fuelExhausted then
    TraceResult.pure (.finished (mergeAtOutOfFuelResult call))
  else if left.len.toNat < trimA.index then
    TraceResult.failure
  else
    let ssa := left.base + trimA.index
    let na := left.len.toNat - trimA.index
    if na = 0 then
      TraceResult.pure (.finished (mergeAtSuccessResult call))
    else
      (TraceResult.sortSliceKeysRead? call.data
        (Int.ofNat (ssa + na - 1))).bind fun lastA =>
        (gallopLeftTraced? call
          (.main call.data (Int.ofNat right.base)) lastA.key
          right.len.toNat (right.len.toNat - 1)).bind fun trimB =>
          mergeAtAfterTrimBTraced call left right firstB lastA trimA trimB

end CPythonListsort
