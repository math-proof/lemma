/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean -/

import Structure.CPythonListsort.Code.Assembly.PowerSortPolicyCost.Part2
import Def.CPythonListsort.Code.Policy.StackPowers.Part2
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant
/-!
# Historical PowerSort invariant for the open scan forest

The machine's pending stack remembers only the power on each open boundary.
It does not remember the internal heap edges of subtrees that have already
been merged.  This module supplies the missing historical invariant carried
by the scan proof: every replay root is aligned with one pending run, is a
source-faithful power tree, and places its outgoing stored boundary below its
internal root power.  The newest root is explicitly a leaf, matching
`found_new_run`'s merge-before-push control flow.

No evaluator induction appears here.  A later bridge must prove preservation
of this invariant from the actual `found_new_run` trace.
-/


namespace CPythonListsort

universe u v

/-- The final root of a nonempty open forest is a literal leaf.  The custom
inductive form makes preservation by prepending older roots explicit, while
also admitting the empty initial forest. -/
inductive NewestRootLeaf : List SpannedMergeTree → Prop
  | empty : NewestRootLeaf []
  | singleton (span : RunSpan) :
      NewestRootLeaf [SpannedMergeTree.leaf span]
  | prepend (entry right : SpannedMergeTree)
      (rest : List SpannedMergeTree)
      (tail : NewestRootLeaf (right :: rest)) :
      NewestRootLeaf (entry :: right :: rest)

end CPythonListsort
