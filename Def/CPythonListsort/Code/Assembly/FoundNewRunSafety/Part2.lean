/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/FoundNewRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.MergeAtSafety.Part4
import Lemma.List.Atlas.CPythonListsort.Code.Policy.FoundNewRunPreservation
import Structure.CPythonListsort.Code.Assembly.FoundNewRunSafety
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

namespace FoundNewRunStableFrame

def foundNewRunUnpoweredOlder : PendingRun :=
  { base := 0, len := 1, power := none }

def foundNewRunUnpoweredNewest : PendingRun :=
  { base := 1, len := 1, power := none }

def foundNewRunUnpoweredRegressionState : MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 3
    basekeys := 0
    data :=
      { entries :=
          #[{ key := 1, value := none },
            { key := 2, value := none },
            { key := 3, value := none }] }
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[foundNewRunUnpoweredOlder, foundNewRunUnpoweredNewest]
    key_compare := fun _ _ => false
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end FoundNewRunStableFrame
end CPythonListsort
