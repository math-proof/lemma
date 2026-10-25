/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Def.CPythonListsort.Code.Assembly.PowerTreeEntropy
import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
import Inductive.CPythonListsort.Code.Assembly.PowerSortPolicyCost
/-!
# PowerSort policy and cost bridge

This module contains the geometry used to turn the implementation's open
merge forest into the min-Cartesian PowerSort tree.  In particular, absorbing
the subtree on the deeper side of three consecutive spans leaves the
shallower boundary power unchanged.  The statements use the same `RunSpan`
and `replayBoundaryPower` objects as the executable policy replay, so no
paper-level midpoint oracle is introduced at the bridge.
-/


namespace CPythonListsort

namespace RunSpan

/-- A reviewable certificate for a scan-produced open PowerSort forest.

`powers` is not inferred from a tree built after the fact: `boundaries`
aligns it with every adjacent pair of open roots and records the exact
transcribed boundary power.  `strict` is the pending-stack heap order, while
`below_left_root` inside `OpenBoundaryCertificate` records the remaining
heap edges into already-built subtrees. -/
structure PowerOpenForestCertificate (input : RunSpan) (start : Nat)
    (forest : List SpannedMergeTree) (powers : List Nat) : Prop where
  inputMax : input.len ≤ PY_LIST_MAX
  spans : OpenSpanChain input start forest
  treeValid : ∀ entry ∈ forest,
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base
  boundaries : OpenBoundaryCertificate input forest powers
  strict : powers.Pairwise (fun earlier later => earlier < later)

end RunSpan
end CPythonListsort
