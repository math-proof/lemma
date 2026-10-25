/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeAtSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeMemoryLifecycle.Part2
import Lemma.List.Atlas.CPythonListsort.Code.Policy.MergeAtPreservation
import Def.CPythonListsort.Code.Assembly.MergeAtSafety
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

structure MergeAtTailSafetyPost (call : MergeState κ ν)
    (execution : TraceResult (MergeAtPreparation κ ν))
    (prepared : MergeAtPreparation κ ν) : Prop where
  resultEq : execution.result = some prepared
  traceSafe : MovementTraceSafe execution
  finishedSuccess : ∀ result, prepared = .finished result →
    result.returnCode = 0 ∧ result.fuelExhausted = false
  stateEq : prepared.state = call

end CPythonListsort
