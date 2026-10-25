/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
/-!
# Logical merge replay and final-collapse cost dominance

`MergeCost` defines the paper-facing merge tree, merge cost, weighted path
length, and their exact equality.  This module adds two pure pieces needed by
the implementation bridge:

* checked replay of the raw, pre-trim logical merge observations; and
* the exact length-and-cost semantics of CPython's `merge_force_collapse`,
  together with a proof that it costs no more than Algorithm 2's canonical
  top-pair completion.

The paper's Algorithm 2 always merges the top pair in its final loop.  CPython
has one additional branch: for a final triple `A, B, C`, it merges `A` with
`B` when `|A| < |C|`.  This is a cost-nonincreasing local tree rotation, not a
tree-equality fact.
-/

/-! ## Checked replay of logical pre-trim merges -/


namespace CPythonListsort

namespace RunSpan

/-- The first index after a run span. -/
def endIndex (span : RunSpan) : Nat :=
  span.base + span.len

/-- The right span begins exactly where the left span ends. -/
def Adjacent (left right : RunSpan) : Prop :=
  left.endIndex = right.base

end RunSpan
end CPythonListsort
