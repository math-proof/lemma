/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortTrace.lean -/

import Def.CPythonListsort.Code.Assembly.BinarysortSafety.Part2
import Def.CPythonListsort.Code.Assembly.CountRunSafety.Part3
import Def.CPythonListsort.Code.Assembly.FoundNewRunSafety.Part2
import Def.CPythonListsort.Code.Assembly.ListSortInputMode
import Def.CPythonListsort.Code.Assembly.ListSortSupport
import Def.CPythonListsort.Code.Assembly.MergeForceCollapseSafety.Part2
import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
/-!
# Traced top-level `list_sort_impl`

This module assembles the genuine top-level access trace from the already
instrumented helper evaluators.  In particular, the scan uses the traced
`count_run`, `binarysort`, `found_new_run`, pending push, and final-collapse
operations directly; it never computes an untraced result and attaches a
synthetic trace afterward.

The two reverse-sort sites intentionally have different physical traces.  The
initial site models CPython's key reversal followed by the saved-list/value
reversal in keyed mode.  The final site models only the reversal of
`saved_ob_item`: synchronized values in keyed mode and keys in unkeyed mode.
Both physical phases erase to the same paired-snapshot semantic reversal.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Initial reverse-sort instrumentation.  Unlike final cleanup, the keyed
case executes both physical phases through the reviewed paired-snapshot
wrapper. -/
def listSortInitialReverseTraced? (state : MergeState κ ν) (inputSize : Nat) :
    TraceResult (ReverseSliceResult κ ν) :=
  sortsliceReverseTraced? state.a.hasValues state.data 0 inputSize

/-- The raw merge-memory boundary emitted by the top-level cleanup.

The two snapshots are computed from the actual state passed to
`mergeFreemem`, rather than reconstructed from its released result. -/
def listSortCleanupMemoryEvent (before : MergeState κ ν) :
    MergeMemoryEvent :=
  .cleanup (MergeMemorySnapshot.ofState before)
    (MergeMemorySnapshot.ofState (mergeFreemem before))

/-- Traced common `succeed`/`fail` cleanup.  The final reversal is one physical
`reverse_slice` call, selected from the retained storage-mode bit.  Every
successful cleanup appends one raw merge-memory boundary after the physical
reverse trace and before returning the post-cleanup state. -/
def finishListSortTraced? (state : MergeState κ ν) (reverse : Bool)
    (inputSize : Nat) (returnCode : Int) (fuelExhausted : Bool) :
    TraceResult (ListSortImplResult κ ν) :=
  if reverse && decide (1 < inputSize) then
    (reverseSlicePhaseTraced? (finalReversePhase state.a.hasValues)
      state.data 0 (Int.ofNat inputSize)).bind fun reversed =>
        let before : MergeState κ ν := { state with data := reversed.slice }
        (TraceResult.pure
          { state := mergeFreemem before
            returnCode := returnCode
            fuelExhausted := fuelExhausted || reversed.fuelExhausted }).appendMemoryEvent
          (listSortCleanupMemoryEvent before)
  else
    (TraceResult.pure
      { state := mergeFreemem state
        returnCode := returnCode
        fuelExhausted := fuelExhausted }).appendMemoryEvent
      (listSortCleanupMemoryEvent state)

/-- Failure adapter for a completed traced `found_new_run` call.  The helper's
trace is composed by the caller; this adapter contributes only the real final
reverse/cleanup trace. -/
def failFromFoundNewRunTraced? (result : FoundNewRunResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    TraceResult (ListSortImplResult κ ν) :=
  finishListSortTraced? result.state reverse inputSize result.returnCode
    result.fuelExhausted

/-- Failure adapter for a completed traced `merge_force_collapse` call. -/
def failFromCollapseTraced? (result : MergeForceCollapseResult κ ν)
    (reverse : Bool) (inputSize : Nat) :
    TraceResult (ListSortImplResult κ ν) :=
  finishListSortTraced? result.state reverse inputSize result.returnCode
    result.fuelExhausted

/-! The following small continuations factor the scan without changing its
control flow.  Each traced helper has an untraced twin used only to make the
structural erasure argument local. -/

/-- Untraced semantic twin of the post-extension continuation.  It is exported
so the top-level safety induction can reason branchwise without unfolding or
duplicating the evaluator. -/
def listSortAfterExtension? (next : MergeState κ ν → Nat → Nat →
    Option (ListSortImplResult κ ν)) (lo remaining : Nat) (reverse : Bool)
    (inputSize : Nat) (extension : MergeState κ ν × Nat × Bool) :
    Option (ListSortImplResult κ ν) :=
  let state := extension.1
  let runLength := extension.2.1
  let extensionFuel := extension.2.2
  if extensionFuel then
    finishListSort? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    none
  else
    match foundNewRun? state runLength with
    | none => none
    | some found =>
        if found.returnCode = 0 ∧ !found.fuelExhausted then
          let newRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          next (pushPendingRun found.state newRun) (lo + runLength)
            (remaining - runLength)
        else
          failFromFoundNewRun? found reverse inputSize

/-- Traced post-extension continuation, including `found_new_run`, the actual
unconditional push, and the recursive scan call. -/
def listSortAfterExtensionTraced?
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (naturalLength target : Nat)
    (extension : MergeState κ ν × Nat × Bool) :
    TraceResult (ListSortImplResult κ ν) :=
  let state := extension.1
  let runLength := extension.2.1
  let extensionFuel := extension.2.2
  if extensionFuel then
    finishListSortTraced? state reverse inputSize (-1) true
  else if runLength = 0 ∨ remaining < runLength then
    TraceResult.failure
  else
    (foundNewRunTraced? state runLength).bind fun found =>
      if found.returnCode = 0 ∧ !found.fuelExhausted then
        let newRun : PendingRun :=
          { base := lo
            len := BitVec.ofNat 64 runLength
            power := none }
        (pushFormedRunTraced found.state newRun naturalLength target
          remaining).bind fun state =>
          next state (lo + runLength) (remaining - runLength)
      else
        failFromFoundNewRunTraced? found reverse inputSize

/-- Untraced semantic twin of the continuation after `count_run`. -/
def listSortAfterCount? (next : MergeState κ ν → Nat → Nat →
    Option (ListSortImplResult κ ν)) (state : MergeState κ ν)
    (lo remaining : Nat) (reverse : Bool) (inputSize : Nat)
    (counted : CountRunResult κ ν) : Option (ListSortImplResult κ ν) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSort? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    none
  else
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
      match binarysort? state state.data (Int.ofNat lo) force runLength with
      | none => none
      | some sorted =>
          listSortAfterExtension? next lo remaining reverse inputSize
            ({ state with data := sorted.slice }, force, sorted.fuelExhausted)
    else
      listSortAfterExtension? next lo remaining reverse inputSize
        (state, runLength, false)

/-- Traced continuation after `count_run`; a short run delegates directly to
the genuine traced `binarysort` before entering the exported post-extension
continuation. -/
def listSortAfterCountTraced?
    (next : MergeState κ ν → Nat → Nat →
      TraceResult (ListSortImplResult κ ν))
    (state : MergeState κ ν) (lo remaining : Nat) (reverse : Bool)
    (inputSize : Nat) (counted : CountRunResult κ ν) :
    TraceResult (ListSortImplResult κ ν) :=
  let state := { state with data := counted.slice }
  if counted.fuelExhausted then
    finishListSortTraced? state reverse inputSize (-1) true
  else if counted.length = 0 ∨ remaining < counted.length then
    TraceResult.failure
  else
    let nextMinrun := minrunNext state.minrunState
    let state := installMinrunState state nextMinrun.state
    let runLength := counted.length
    let target := nextMinrun.result.toNat
    let force := if remaining ≤ target then remaining else target
    if (BitVec.ofNat 64 runLength : PySSize).slt nextMinrun.result then
      (binarysortTraced? state state.data (Int.ofNat lo) force runLength).bind
        fun sorted =>
          listSortAfterExtensionTraced? next lo remaining reverse inputSize
            counted.length target
            ({ state with data := sorted.slice }, force, sorted.fuelExhausted)
    else
      listSortAfterExtensionTraced? next lo remaining reverse inputSize
        counted.length target
        (state, runLength, false)

/-- The traced run-discovery loop.  Its recursive shape and branch order mirror
`listSortScan?`; every local trace is composed at the point where the matching
C helper runs. -/
def listSortScanTraced? :
    Nat → MergeState κ ν → Nat → Nat → Bool → Nat →
      TraceResult (ListSortImplResult κ ν)
  | 0, state, _, remaining, reverse, inputSize =>
      if remaining = 0 then
        (mergeForceCollapseTraced? state).bind fun collapsed =>
          if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
            finishListSortTraced? collapsed.state reverse inputSize 0 false
          else
            failFromCollapseTraced? collapsed reverse inputSize
      else
        (finishListSortTraced? state reverse inputSize (-1) true).markFuelExhausted
  | fuel + 1, state, lo, remaining, reverse, inputSize =>
      if remaining = 0 then
        (mergeForceCollapseTraced? state).bind fun collapsed =>
          if collapsed.returnCode = 0 ∧ !collapsed.fuelExhausted then
            finishListSortTraced? collapsed.state reverse inputSize 0 false
          else
            failFromCollapseTraced? collapsed reverse inputSize
      else
        (countRunTraced? state state.data (Int.ofNat lo) remaining).bind fun counted =>
          listSortAfterCountTraced?
            (fun state lo remaining =>
              listSortScanTraced? fuel state lo remaining reverse inputSize)
            state lo remaining reverse inputSize counted

def listSortZeroFuelRegressionSlice : SortSlice Nat PUnit :=
  { entries :=
      #[{ key := 2, value := none },
        { key := 1, value := none }] }

def listSortZeroFuelRegressionState : MergeState Nat PUnit :=
  (initialMergeState (fun left right : Nat => decide (left < right)) false
    listSortZeroFuelRegressionSlice).1

/-- Genuine traced snapshot-model `list_sort_impl`.  Initial reverse-sort
instrumentation uses `sortsliceReverseTraced?`: keyed execution records the key
phase followed by the synchronized-values phase, both from the same paired
snapshot. -/
def listSortImplTraced? (lt : BoolComparator κ) (reverse hasKeyfunc : Bool)
    (input : SortSlice κ ν) : TraceResult (ListSortImplResult κ ν) :=
  if input.entries.size ≤ PY_LIST_MAX then
    let initialized := initialMergeState lt hasKeyfunc input
    let state := initialized.1
    let execution :=
      if !initialized.2 then
        (finishListSortTraced? state reverse input.entries.size (-1) true).markFuelExhausted
      else if input.entries.size < 2 then
        finishListSortTraced? state reverse input.entries.size 0 false
      else if reverse then
        (listSortInitialReverseTraced? state input.entries.size).bind fun reversed =>
            let state := { state with data := reversed.slice }
            if reversed.fuelExhausted then
              finishListSortTraced? state reverse input.entries.size (-1) true
            else
              listSortScanTraced? input.entries.size state 0 input.entries.size
                reverse input.entries.size
      else
        listSortScanTraced? input.entries.size state 0 input.entries.size reverse
          input.entries.size
    execution.prependMemoryEvent
      (.initial (MergeMemorySnapshot.ofState state))
  else
    TraceResult.failure

/-- Public traced wrapper for proof-carrying keyed or unkeyed input. -/
def listSortTraced? (lt : BoolComparator κ) (reverse : Bool)
    (input : ListSortInput κ ν) : TraceResult (ListSortImplResult κ ν) :=
  listSortImplTraced? lt reverse input.hasKeyfunc input.slice

/-! ## Formed-run event anti-vacuity -/

def formedRunPolicyRegressionInput : SortSlice Nat Unit :=
  { entries :=
      #[{ key := 1, value := none },
        { key := 2, value := none },
        { key := 3, value := none }] }

def formedRunExtensionRegressionInput : SortSlice Nat Unit :=
  { entries :=
      #[{ key := 3, value := none },
        { key := 1, value := none },
        { key := 2, value := none },
        { key := 4, value := none },
        { key := 5, value := none },
        { key := 6, value := none },
        { key := 7, value := none },
        { key := 8, value := none }] }

end CPythonListsort
