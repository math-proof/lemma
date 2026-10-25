/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeForceCollapseSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeForceCollapsePreservation
/-!
# `merge_force_collapse` safety

This module traces the neighboring pending-run reads performed by the reviewed
sequential Lean transcription of `merge_force_collapse` and composes them with
the complete trace of each delegated `merge_at` call.  This is an exact order
claim about the Lean model; it does not impose an evaluation order on the two
operands of C's `<` operator.  The public safety theorem proves that the
pending-depth fuel supplied by the transcription is adequate for every
nonempty valid layout.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

def mergeForceCollapseSuccessResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

def mergeForceCollapseOutOfFuelResult (state : MergeState κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

def mergeForceCollapseFromMergeAt (result : MergeAtResult κ ν) :
    MergeForceCollapseResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Traced form of the source's merge-position choice.  When there are at
least three pending runs, the reviewed sequential Lean model records the lower
neighbor and then the upper neighbor.  This is not a claim about C operand
evaluation order. -/
def forceCollapseIndexTraced? (state : MergeState κ ν) : TraceResult Nat :=
  if 1 < state.pending.size then
    let i := state.pending.size - 2
    if 0 < i then
      (TraceResult.pendingRunRead? state (Int.ofNat (i - 1))).bind fun previous =>
        (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).map fun following =>
          if previous.len.slt following.len then i - 1 else i
    else
      TraceResult.pure i
  else
    TraceResult.failure

/-- Fuel-bounded traced collapse loop.  Exhaustion is observable both in its
result and in the trace. -/
def mergeForceCollapseLoopTraced? :
    Nat → MergeState κ ν → TraceResult (MergeForceCollapseResult κ ν)
  | 0, state =>
      if state.pending.size ≤ 1 then
        TraceResult.pure (mergeForceCollapseSuccessResult state)
      else
        (TraceResult.pure
          (mergeForceCollapseOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state =>
      if 1 < state.pending.size then
        (forceCollapseIndexTraced? state).bind fun i =>
          (mergeAtTraced? state i).bind fun merged =>
            if merged.returnCode = 0 ∧ !merged.fuelExhausted then
              mergeForceCollapseLoopTraced? fuel merged.state
            else
              TraceResult.pure (mergeForceCollapseFromMergeAt merged)
      else
        TraceResult.pure (mergeForceCollapseSuccessResult state)

/-- Fully traced `merge_force_collapse` evaluator. -/
def mergeForceCollapseTraced? (state : MergeState κ ν) :
    TraceResult (MergeForceCollapseResult κ ν) :=
  mergeForceCollapseLoopTraced? state.pending.size state

end CPythonListsort
