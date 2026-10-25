/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Structure.CPythonListsort.Code.Assembly.MergeAtSafety.Part2
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

namespace MergeAtStableFrame

/-- Execute the traced merge continuation selected by
`prepareMergeAtTraced?`.  A successful directional continuation appends
exactly one raw call record computed from its actual result. -/
def finishMergeAtPreparationTraced? :
    MergeAtPreparation κ ν → TraceResult (MergeAtResult κ ν)
  | .finished result => TraceResult.pure result
  | .mergeLo call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeLoTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeLoMemoryCallEvent call result))).map
        mergeAtFromLo
  | .mergeHi call =>
      (TraceResult.recordSuccessMemoryEvent
        (mergeHiTraced? call.state call.ssa call.ssb call.na call.nb)
        (fun result =>
          .mergeCall
            (MergeMemoryCallEvent.mergeHiMemoryCallEvent call result))).map
        mergeAtFromHi

/-- Fully traced `merge_at` evaluator. -/
def mergeAtTraced? (state : MergeState κ ν) (i : Nat) :
    TraceResult (MergeAtResult κ ν) :=
  (prepareMergeAtTraced? state i).bind finishMergeAtPreparationTraced?

end MergeAtStableFrame
end CPythonListsort
