/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Def.CPythonListsort.Code.Assembly.MergeCost
/-!
# Merge-cost accounting

This module isolates the implementation-independent arithmetic behind the
Munro--Wild PowerSort merge-cost bound.  Run lengths and merge costs remain
natural numbers; entropy and the final inequality live in `ℝ`.

An empty `MergePlan` represents the empty input.  A nonempty plan is a binary
tree whose leaves are the runs, in input order.  Internal powers are retained
for the later PowerSort-policy bridge but do not affect merge-cost accounting.
-/


namespace CPythonListsort

/-- A binary merge tree.  Leaves store run lengths and each internal node
retains its PowerSort node power for the later policy bridge. -/
inductive MergeTree where
  | leaf (length : Nat)
  | merge (power : Nat) (left right : MergeTree)
  deriving DecidableEq, Repr

end CPythonListsort
