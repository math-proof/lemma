/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
import Structure.CPythonListsort.Code.Assembly.MergeTreeCost
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

namespace SpannedMergeTree

/-- The tree's leaf weights account for exactly the paired source span. -/
def Valid (entry : SpannedMergeTree) : Prop :=
  entry.tree.totalLength = entry.span.len

/-- Initial forest entry for one implementation-formed run. -/
def leaf (span : RunSpan) : SpannedMergeTree :=
  { span := span, tree := .leaf span.len }

/-- Logical combination of two adjacent forest entries.  The supplied power
is a semantic label only and does not affect merge-cost accounting. -/
def merge (power : Nat) (left right : SpannedMergeTree) : SpannedMergeTree :=
  { span := left.span.merge right.span
    tree := .merge power left.tree right.tree }

end SpannedMergeTree
end CPythonListsort
