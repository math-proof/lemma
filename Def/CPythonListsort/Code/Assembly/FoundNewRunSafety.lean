/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.FoundNewRunPreservation
/-!
# `found_new_run` safety

This module traces the pending-stack reads, the delegated `merge_at` calls,
and the final top-power write performed by `found_new_run`.  Power computation
has no indexed-memory event of its own.  Exhausting either explicit bound is
recorded in the trace, while the public theorem proves that source-admitted
executions never take either exhaustion branch.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

def foundNewRunSuccessResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := 0, fuelExhausted := false }

def foundNewRunOutOfFuelResult (state : MergeState κ ν) :
    FoundNewRunResult κ ν :=
  { state := state, returnCode := -1, fuelExhausted := true }

def foundNewRunFromMergeAt (result : MergeAtResult κ ν) :
    FoundNewRunResult κ ν :=
  { state := result.state
    returnCode := result.returnCode
    fuelExhausted := result.fuelExhausted }

/-- Trace the single C field write which initializes the current top run's
power.  Constructing the replacement record does not add a synthetic read. -/
def setTopPowerTraced? (state : MergeState κ ν) (power : Nat) :
    TraceResult (MergeState κ ν) :=
  if state.pending.isEmpty then
    TraceResult.failure
  else
    TraceResult.pendingRunPowerWrite? state
      (Int.ofNat (state.pending.size - 1)) power

/-- Traced collapse loop used by `foundNewRunTraced?`. -/
def foundNewRunLoopTraced? :
    Nat → MergeState κ ν → Nat → TraceResult (FoundNewRunResult κ ν)
  | 0, state, _ =>
      (TraceResult.pure (foundNewRunOutOfFuelResult state)).markFuelExhausted
  | fuel + 1, state, power =>
      if 1 < state.pending.size then
        (TraceResult.pendingRunRead? state
          (Int.ofNat (state.pending.size - 2))).bind fun preceding =>
            match preceding.power with
            | none => TraceResult.failure
            | some precedingPower =>
                if power < precedingPower then
                  (mergeAtTraced? state (state.pending.size - 2)).bind fun merged =>
                    if merged.returnCode = 0 ∧ !merged.fuelExhausted then
                      foundNewRunLoopTraced? fuel merged.state power
                    else
                      TraceResult.pure (foundNewRunFromMergeAt merged)
                else
                  (setTopPowerTraced? state power).map foundNewRunSuccessResult
      else
        (setTopPowerTraced? state power).map foundNewRunSuccessResult

/-- Fully traced `found_new_run` evaluator. -/
def foundNewRunTraced? (state : MergeState κ ν) (n2 : Nat) :
    TraceResult (FoundNewRunResult κ ν) :=
  if state.pending.isEmpty then
    TraceResult.pure (foundNewRunSuccessResult state)
  else
    (TraceResult.pendingRunRead? state
      (Int.ofNat (state.pending.size - 1))).bind fun top =>
        if (!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
            (0 : PySSize).slt top.len && decide (0 < n2) &&
            decide (n2 ≤ PY_SSIZE_T_MAX) &&
            decide (top.base - state.basekeys + top.len.toNat + n2 ≤
              state.listlen.toNat) then
          let powered := powerloopTraced
            (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
            (BitVec.ofNat 64 n2) state.listlen
          if !powered.stopped then
            (TraceResult.pure
              (foundNewRunOutOfFuelResult state)).markFuelExhausted
          else
            foundNewRunLoopTraced? state.pending.size state powered.result
        else
          TraceResult.failure

end CPythonListsort
