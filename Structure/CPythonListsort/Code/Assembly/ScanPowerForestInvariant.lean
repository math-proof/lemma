/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean -/

import Structure.CPythonListsort.Code.Assembly.PowerSortPolicyCost.Part2
import Def.CPythonListsort.Code.Policy.StackPowers.Part2
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

/-- Historical facts connecting one open replay root to its current pending
run.  The final clause is vacuous for a leaf and records the heap edge that is
otherwise lost when an internal subtree is summarized by one pending run. -/
structure RunTreeAligned (input : RunSpan) (entry : SpannedMergeTree)
    (run : PendingRun) : Prop where
  span_eq : entry.span = RunSpan.ofPendingRun run
  valid : entry.Valid
  powerValid : entry.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) entry.span.base
  outgoingBelowRoot : ∀ boundaryPower rootPower,
    run.power = some boundaryPower →
      entry.tree.rootPower = some rootPower → boundaryPower < rootPower

end CPythonListsort
