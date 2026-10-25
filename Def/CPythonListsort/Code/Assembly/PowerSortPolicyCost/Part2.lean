/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Def.CPythonListsort.Code.Assembly.PowerTreeEntropy
import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
import Structure.CPythonListsort.Code.Assembly.PowerSortPolicyCost
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

/-- The top-level scan certificate starts at the input base. -/
def PowerOpenForestValid (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  ∃ powers, PowerOpenForestCertificate input input.base forest powers

/-- Right-associated tree obtained by repeatedly merging the top pair of a
nonempty open forest.  Its node label is recomputed from the full aggregate
child spans, rather than copied from certificate metadata. -/
def canonicalTopPairRoot (input : RunSpan) :
    SpannedMergeTree → List SpannedMergeTree → SpannedMergeTree
  | current, [] => current
  | current, next :: rest =>
      let right := canonicalTopPairRoot input next rest
      SpannedMergeTree.merge
        (replayBoundaryPower input current.span right.span) current right

/-- Empty-or-tree normalization of canonical repeated-top-pair completion. -/
def canonicalTopPairCompletion (input : RunSpan) :
    List SpannedMergeTree → MergePlan
  | [] => .empty
  | first :: rest => .tree (canonicalTopPairRoot input first rest).tree

end RunSpan
end CPythonListsort
