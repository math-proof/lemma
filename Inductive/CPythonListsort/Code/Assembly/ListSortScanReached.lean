/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortScanReached.lean -/

import Def.CPythonListsort.Code.Assembly.ListSortTrace
/-!
# Control-flow provenance for the final-collapse call

The logical policy-event projection does not retain the machine state passed
to `merge_force_collapse`.  This module records that state separately, by
following the successful `TraceResult.bind` path of the genuine traced scan.
The certificate is intentionally independent of policy events: policy-free
helper prefixes can wrap it only when their actual result selects the certified
continuation.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- `openState` is the actual state at a successful terminal scan call, hence
the state passed by that call to `mergeForceCollapseTraced?`.

`bindPrefix` preserves this provenance through a genuine successful helper
prefix.  In particular, it cannot transport the certificate merely because
two executions happen to have equal policy-event projections. -/
inductive ListSortScanReachedCollapse
    (reverse : Bool) (inputSize : Nat)
    (openState : MergeState κ ν)
    (collapsed : MergeForceCollapseResult κ ν) :
    TraceResult (ListSortImplResult κ ν) → Prop where
  | terminal (fuel lo : Nat)
      (hcollapse :
        (mergeForceCollapseTraced? openState).result = some collapsed)
      (hcode : collapsed.returnCode = 0)
      (hfuel : collapsed.fuelExhausted = false) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (listSortScanTraced? fuel openState lo 0 reverse inputSize)
  | bindPrefix {α : Type (max u v)}
      (before : TraceResult α)
      (next : α → TraceResult (ListSortImplResult κ ν))
      (value : α)
      (hbefore : before.result = some value)
      (tail :
        ListSortScanReachedCollapse reverse inputSize openState collapsed
          (next value)) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (before.bind next)
  | prependMemoryEvent
      (execution : TraceResult (ListSortImplResult κ ν))
      (event : MergeMemoryEvent)
      (tail :
        ListSortScanReachedCollapse reverse inputSize openState collapsed
          execution) :
      ListSortScanReachedCollapse reverse inputSize openState collapsed
        (execution.prependMemoryEvent event)

end CPythonListsort
