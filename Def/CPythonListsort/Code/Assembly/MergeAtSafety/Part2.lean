/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Structure.CPythonListsort.Code.Assembly.MergeAtSafety
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

/-- Traced prefix of `merge_at`: pending-stack selection and mutation, both
endpoint reads, both trimming gallops, and the final dispatch decision. -/
def prepareMergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtPreparation κ ν) :=
  if 2 ≤ state.pending.size ∧
      (i + 2 = state.pending.size ∨ i + 3 = state.pending.size) then
    (TraceResult.pendingRunRead? state (Int.ofNat i)).bind fun left =>
      (TraceResult.pendingRunRead? state (Int.ofNat (i + 1))).bind fun right =>
        if (0 : PySSize).slt left.len ∧ (0 : PySSize).slt right.len ∧
            left.base + left.len.toNat = right.base then
          (mergeAtPendingUpdateTraced? state i left right).bind fun call =>
            (TraceResult.sortSliceKeysRead? call.data
              (Int.ofNat right.base)).bind fun firstB =>
              (gallopRightTraced? call
                (.main call.data (Int.ofNat left.base)) firstB.key
                left.len.toNat 0).bind fun trimA =>
                mergeAtAfterTrimATraced call left right firstB trimA
        else
          TraceResult.failure
  else
    TraceResult.failure

/-- The exact source-order trace prefix on a preparation path which reaches a
merge continuation.  The first gallop's result determines the last-A endpoint
read used to start the second gallop. -/
def mergeAtPreparationDispatchTrace (pre : MergeState κ ν) (i : Nat)
    (call : MergeAtCall κ ν) : AccessTrace :=
  (TraceResult.pendingRunRead? pre (Int.ofNat i)).trace.compose
    ((TraceResult.pendingRunRead? pre (Int.ofNat (i + 1))).trace.compose
      ((mergeAtPendingUpdateTraced? pre i call.left call.right).trace.compose
        ((TraceResult.sortSliceKeysRead? call.state.data
          (Int.ofNat call.right.base)).trace.compose
          ((gallopRightTraced? call.state
            (.main call.state.data (Int.ofNat call.left.base)) call.firstB.key
            call.left.len.toNat 0).trace.compose
            ((TraceResult.sortSliceKeysRead? call.state.data
              (Int.ofNat (call.left.base + call.trimA.index + call.na - 1))).trace.compose
              (gallopLeftTraced? call.state
                (.main call.state.data (Int.ofNat call.right.base)) call.lastA.key
                call.right.len.toNat (call.right.len.toNat - 1)).trace)))))

end CPythonListsort
