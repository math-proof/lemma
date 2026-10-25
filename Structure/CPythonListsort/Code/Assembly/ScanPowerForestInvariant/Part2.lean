/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean -/

import Structure.CPythonListsort.Code.Assembly.PowerSortPolicyCost.Part2
import Def.CPythonListsort.Code.Policy.StackPowers.Part2
import Inductive.CPythonListsort.Code.Assembly.ScanPowerForestInvariant
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

/-- The scan-carried historical certificate for an open merge forest.

`basekeys_eq` and `listlen_eq` are the exact machine/input frame.  `aligned`
keeps forest roots and pending runs in lockstep; unlike a span-only matching
predicate, it retains each root's internal PowerSort validity and the missing
heap edge from the outgoing pending power into that root. -/
structure ScanPowerForestInv (input : RunSpan)
    (forest : List SpannedMergeTree) (state : MergeState κ ν) : Prop where
  inputMax : input.len ≤ PY_LIST_MAX
  basekeys_eq : state.basekeys = input.base
  listlen_eq : state.listlen = BitVec.ofNat 64 input.len
  aligned : List.Forall₂ (RunTreeAligned input) forest state.pending.toList
  newestRootLeaf : NewestRootLeaf forest

end CPythonListsort
