/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part2
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

set_option maxHeartbeats 5000000 in
set_option linter.flexible false in

/-- State fields which `merge_at` is forbidden to mutate.  The pending stack,
main data contents, temporary allocation, and adaptive `min_gallop` output are
intentionally absent because the operation may change them. -/
structure MergeAtStableFrame (before after : MergeState κ ν) : Prop where
  listlen : after.listlen = before.listlen
  basekeys : after.basekeys = before.basekeys
  dataSize : after.data.entries.size = before.data.entries.size
  tempValuesMode : after.a.hasValues = before.a.hasValues
  comparator : after.key_compare = before.key_compare
  mrCurrent : after.mr_current = before.mr_current
  mrE : after.mr_e = before.mr_e
  mrMask : after.mr_mask = before.mr_mask

namespace MergeAtStableFrame

/-- Safety facts at the boundary between `merge_at`'s trimming prefix and its
selected merge continuation. -/
structure MergeAtPreparationSafetyPost (pre : MergeState κ ν) (i : Nat)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  exactErasure : execution.erase = prepareMergeAt? pre i
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  tempInvariant : TempStorageInv prepared.state.a prepared.state.alloced
  tempLive : prepared.state.a.Live
  valuesMode :
    SortSlice.ValuesModeInvariant prepared.state.a.hasValues prepared.state.data
  hasValuesFrame : prepared.state.a.hasValues = pre.a.hasValues
  storageFrame : prepared.state.a = pre.a
  allocedFrame : prepared.state.alloced = pre.alloced
  dataFrame : prepared.state.data = pre.data
  stableFrame : MergeAtStableFrame pre prepared.state

end MergeAtStableFrame
end CPythonListsort
