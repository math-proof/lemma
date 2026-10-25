/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean -/

import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9
import Def.CPythonListsort.Code.Assembly.MergeCost.Part3
import Theorem.CPythonListsort.Code.Assembly.MergeTreeCost
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

/-! ## CPython final-collapse cost relation -/

/-- Source-faithful length-and-cost semantics of `merge_force_collapse`.

For at least three pending runs, `a`, `b`, and `c` are the final three lengths.
The strict source guard chooses the third-last pair exactly when `a < c`;
otherwise the top pair is merged. -/
inductive CPythonForceCollapseCost : List Nat → Nat → Prop
  | empty : CPythonForceCollapseCost [] 0
  | singleton (length : Nat) : CPythonForceCollapseCost [length] 0
  | pair (left right : Nat) :
      CPythonForceCollapseCost [left, right] (left + right)
  | mergeTop (before : List Nat) (a b c tailCost : Nat)
      (hselect : ¬a < c)
      (tail : CPythonForceCollapseCost (before ++ [a, b + c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (b + c + tailCost)
  | mergeThirdLast (before : List Nat) (a b c tailCost : Nat)
      (hselect : a < c)
      (tail : CPythonForceCollapseCost (before ++ [a + b, c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (a + b + tailCost)

end SpannedMergeTree
end CPythonListsort
