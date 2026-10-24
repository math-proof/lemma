import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.ListSortScanReached
open CPythonListsort CPythonListsort.ListSortScanReachedCollapse


namespace CPythonListsort.ListSortScanReachedCollapse

/--
[of_execution_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortScanReached.lean)
-/
@[path]
lemma of_execution_eq
  {κ : Type u}
  {ν : Type v}
  {reverse : Bool}
  {inputSize : Nat}
  {openState : MergeState κ ν}
  {collapsed : MergeForceCollapseResult κ ν}
  {first second : TraceResult (ListSortImplResult κ ν)}
  {reached : ListSortScanReachedCollapse reverse inputSize openState collapsed first}
-- given
  (hExecution : first = second) :
-- imply
  ListSortScanReachedCollapse reverse inputSize openState collapsed second := by
-- proof
  subst second
  exact reached

end CPythonListsort.ListSortScanReachedCollapse

namespace CPythonListsort.ListSortScanReachedCollapse

/--
[through_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortScanReached.lean)
-/
@[path]
lemma through_bind
  {κ : Type u}
  {ν : Type v}
  {reverse : Bool}
  {inputSize : Nat}
  {openState : MergeState κ ν}
  {collapsed : MergeForceCollapseResult κ ν}
  {α : Type (max u v)}
  {before : TraceResult α}
  {next : α → TraceResult (ListSortImplResult κ ν)}
  {value : α}
  {tail : ListSortScanReachedCollapse reverse inputSize openState collapsed (next value)}
-- given
  (hbefore : before.result = some value) :
-- imply
  ListSortScanReachedCollapse reverse inputSize openState collapsed (before.bind next) :=
-- proof
  .bindPrefix before next value hbefore tail

end CPythonListsort.ListSortScanReachedCollapse

namespace CPythonListsort.ListSortScanReachedCollapse

/--
[collapse_result_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortScanReached.lean)
-/
@[path]
lemma collapse_result_eq
  {κ : Type u}
  {ν : Type v}
  {reverse : Bool}
  {inputSize : Nat}
  {openState : MergeState κ ν}
  {collapsed : MergeForceCollapseResult κ ν}
  {execution : TraceResult (ListSortImplResult κ ν)}
  {reached : ListSortScanReachedCollapse reverse inputSize openState collapsed execution} :
-- imply
  (mergeForceCollapseTraced? openState).result = some collapsed := by
-- proof
  induction reached with
  | terminal _ _ hcollapse _ _ => exact hcollapse
  | bindPrefix _ _ _ _ _ ih => exact ih
  | prependMemoryEvent _ _ _ ih => exact ih

end CPythonListsort.ListSortScanReachedCollapse

namespace CPythonListsort.ListSortScanReachedCollapse

/--
[collapse_succeeded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortScanReached.lean)
-/
@[path]
lemma collapse_succeeded
  {κ : Type u}
  {ν : Type v}
  {reverse : Bool}
  {inputSize : Nat}
  {openState : MergeState κ ν}
  {collapsed : MergeForceCollapseResult κ ν}
  {execution : TraceResult (ListSortImplResult κ ν)}
  {reached : ListSortScanReachedCollapse reverse inputSize openState collapsed execution} :
-- imply
  collapsed.returnCode = 0 ∧ collapsed.fuelExhausted = false := by
-- proof
  induction reached with
  | terminal _ _ _ hcode hfuel => exact ⟨hcode, hfuel⟩
  | bindPrefix _ _ _ _ _ ih => exact ih
  | prependMemoryEvent _ _ _ ih => exact ih

end CPythonListsort.ListSortScanReachedCollapse


-- created on 2026-10-23
